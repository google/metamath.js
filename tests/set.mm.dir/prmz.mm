include "cprime.mm"
include "wcel.mm"
include "prmnn.mm"
include "nnzd.mm"

theorem prmz
  let cP: class P
  let vn: setvar n
  let vp: setvar p
  let vz: setvar z


  assert |- ( P e. Prime -> P e. ZZ )

  proof
    cP
    cprime
    wcel
    cP
    cP
    prmnn
    nnzd
end
