include "ax-r4.mm"

theorem con4
  let wva: term a
  let wvb: term b
  assume con4.1: |- a = b


  assert |- a ' = b '

  proof
    wva
    wvb
    con4.1
    ax-r4
end
