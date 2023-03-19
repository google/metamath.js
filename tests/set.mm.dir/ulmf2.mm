include "wfn.mm"
include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cz.mm"
include "cpm.mm"
include "wcel.mm"
include "ulmpm.mm"
include "wss.mm"
include "ovex.mm"
include "zex.mm"
include "elpm2.mm"
include "simplbi.mm"
include "syl.mm"
include "adantl.mm"
include "wceq.mm"
include "fndm.mm"
include "adantr.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem ulmf2
  let cS: class S
  let cF: class F
  let cG: class G
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z


  assert |- ( ( F Fn Z /\ F ( ~~>u ` S ) G ) -> F : Z --> ( CC ^m S ) )

  proof
    cF
    cZ
    wfn
    #
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    wa
    #
    cF
    cdm
    #
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    cZ
    @4
    cF
    wf
    @1
    @5
    @0
    @1
    cF
    @4
    cz
    cpm
    co
    wcel
    #
    @5
    cS
    cF
    cG
    ulmpm
    @6
    @5
    @3
    cz
    wss
    @4
    cz
    cF
    cc
    cS
    cmap
    ovex
    zex
    elpm2
    simplbi
    syl
    adantl
    @2
    @3
    cZ
    @4
    cF
    @0
    @3
    cZ
    wceq
    @1
    cZ
    cF
    fndm
    adantr
    feq2d
    mpbid
end
