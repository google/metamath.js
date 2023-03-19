include "cgbow.mm"
include "wcel.mm"
include "codd.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "isgbow.mm"
include "simplbi.mm"

theorem gbowodd
  let cZ: class Z
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOddW -> Z e. Odd )

  proof
    cZ
    cgbow
    wcel
    cZ
    codd
    wcel
    cZ
    vp
    cv
    vq
    cv
    caddc
    co
    vr
    cv
    caddc
    co
    wceq
    vr
    cprime
    wrex
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    cZ
    vr
    vq
    vp
    isgbow
    simplbi
end
