include "u1lemab.mm"

theorem lem4.6.2e2
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) )

  proof
    wva
    wvb
    u1lemab
end
