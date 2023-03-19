include "i3le.mm"

theorem u3lemle2
  param wva: term a
  param wvb: term b
  assume u3lemle2.1: |- ( a ->3 b ) = 1


  assert |- a =< b

  proof
    wva
    wvb
    u3lemle2.1
    i3le
end
