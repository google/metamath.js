include "u12lem.mm"

theorem lem4.6.6i1j2
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->1 b ) v ( a ->2 b ) ) = ( a ->0 b )

  proof
    wva
    wvb
    u12lem
end
