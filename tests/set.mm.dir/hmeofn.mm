include "ctop.mm"
include "cv.mm"
include "ccnv.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "crab.mm"
include "chmeo.mm"
include "df-hmeo.mm"
include "ovex.mm"
include "rabex.mm"
include "fnmpt2i.mm"

theorem hmeofn
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let cJ: class J
  let cK: class K


  assert |- Homeo Fn ( Top X. Top )

  proof
    vj
    vk
    ctop
    ctop
    vf
    cv
    ccnv
    vk
    cv
    #
    vj
    cv
    #
    ccn
    co
    wcel
    #
    vf
    @1
    @0
    ccn
    co
    #
    crab
    chmeo
    vf
    vj
    vk
    df-hmeo
    @2
    vf
    @3
    @1
    @0
    ccn
    ovex
    rabex
    fnmpt2i
end
