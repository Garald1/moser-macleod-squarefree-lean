-- Convert GitHub-flavoured display-math fences to real display mathematics,
-- and turn wide Markdown tables into wrapping lists suitable for a PDF page.

function CodeBlock(block)
  if block.classes:includes("math") then
    return pandoc.Para({pandoc.Math("DisplayMath", block.text)})
  end
  if block.classes:includes("mermaid") then
    return pandoc.BulletList({
      {pandoc.Plain({pandoc.Str("Möbius Dirichlet series and elementary Mertens bounds yield the tail estimate.")})},
      {pandoc.Plain({pandoc.Str("The tail estimate and square-divisor identity yield the coarse bound for N ≥ 401.")})},
      {pandoc.Plain({pandoc.Str("The 400-cell rational certificate handles every real x with 1 ≤ x < 401.")})},
      {pandoc.Plain({pandoc.Str("The finite certificate and coarse range combine to prove |R(x)| < √x for every x > 0.")})}
    })
  end
end

function Header(header)
  if header.level == 1 and pandoc.utils.stringify(header.content) == "Human proof and Lean correspondence" then
    return {}
  end
  header.level = math.max(1, header.level - 1)
  return header
end

local function append_inlines(target, source)
  for _, inline in ipairs(source) do
    table.insert(target, inline)
  end
end

local function cell_inlines(cell)
  local result = {}
  for _, block in ipairs(cell.contents) do
    if block.t == "Plain" or block.t == "Para" then
      if #result > 0 then table.insert(result, pandoc.Space()) end
      append_inlines(result, block.content)
    end
  end
  return result
end

function Table(tbl)
  local headers = {}
  if #tbl.head.rows > 0 then
    for _, cell in ipairs(tbl.head.rows[1].cells) do
      table.insert(headers, cell_inlines(cell))
    end
  end

  local items = {}
  for _, body in ipairs(tbl.bodies) do
    for _, row in ipairs(body.body) do
      local line = {}
      if #row.cells > 0 then
        table.insert(line, pandoc.Strong(cell_inlines(row.cells[1])))
      end
      for index = 2, #row.cells do
        table.insert(line, pandoc.Str(index == 2 and ":" or ";"))
        table.insert(line, pandoc.Space())
        if headers[index] and #headers[index] > 0 then
          table.insert(line, pandoc.Emph(headers[index]))
          table.insert(line, pandoc.Str(":"))
          table.insert(line, pandoc.Space())
        end
        append_inlines(line, cell_inlines(row.cells[index]))
      end
      table.insert(items, {pandoc.Plain(line)})
    end
  end
  return pandoc.BulletList(items)
end
