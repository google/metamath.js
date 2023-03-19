include "kt.mm"
include "ax-trud.mm"
include "syl.mm"

theorem a1i
  param ta: term A
  param tr: term R
  assume ax-trud.1: |- R : bool
  assume ax-a1i.2: |- T. |= A


  assert |- R |= A

  proof
    tr
    kt
    ta
    tr
    ax-trud.1
    ax-trud
    ax-a1i.2
    syl
end
