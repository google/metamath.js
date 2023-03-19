include "ccom.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wss.mm"
include "crn.mm"
include "cres.mm"
include "wceq.mm"
include "wf1.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "dprdres.mm"
include "simpld.mm"
include "csubg.mm"
include "cfv.mm"
include "dprdf2.mm"
include "fssresd.mm"
include "fdm.mm"
include "syl.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "dprdf1o.mm"
include "ssid.mm"
include "cores.mm"
include "ax-mp.mm"
include "syl6breq.mm"
include "oveq2i.mm"
include "simprd.mm"
include "syl5eqr.mm"
include "eqsstrd.mm"
include "jca.mm"

theorem dprdf1
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  assume dprdf1.1: |- ( ph -> G dom DProd S )
  assume dprdf1.2: |- ( ph -> dom S = I )
  assume dprdf1.3: |- ( ph -> F : J -1-1-> I )


  assert |- ( ph -> ( G dom DProd ( S o. F ) /\ ( G DProd ( S o. F ) ) C_ ( G DProd S ) ) )

  proof
    wph
    cG
    cS
    cF
    ccom
    #
    cdprd
    cdm
    #
    wbr
    cG
    @0
    cdprd
    co
    #
    cG
    cS
    cdprd
    co
    #
    wss
    wph
    cG
    cS
    cF
    crn
    #
    cres
    #
    cF
    ccom
    #
    @0
    @1
    wph
    cG
    @6
    @1
    wbr
    #
    cG
    @6
    cdprd
    co
    #
    cG
    @5
    cdprd
    co
    #
    wceq
    #
    wph
    @5
    cF
    cG
    @4
    cJ
    wph
    cG
    @5
    @1
    wbr
    #
    @9
    @3
    wss
    #
    wph
    @4
    cS
    cG
    cI
    dprdf1.1
    dprdf1.2
    wph
    cJ
    cI
    cF
    wf1
    #
    cJ
    cI
    cF
    wf
    @4
    cI
    wss
    dprdf1.3
    cJ
    cI
    cF
    f1f
    cJ
    cI
    cF
    frn
    3syl
    #
    dprdres
    #
    simpld
    wph
    @4
    cG
    csubg
    cfv
    #
    @5
    wf
    @5
    cdm
    @4
    wceq
    wph
    cI
    @16
    @4
    cS
    wph
    cS
    cG
    cI
    dprdf1.1
    dprdf1.2
    dprdf2
    @14
    fssresd
    @4
    @16
    @5
    fdm
    syl
    wph
    @13
    cJ
    @4
    cF
    wf1o
    dprdf1.3
    cJ
    cI
    cF
    f1f1orn
    syl
    dprdf1o
    #
    simpld
    @4
    @4
    wss
    @6
    @0
    wceq
    @4
    ssid
    cS
    cF
    @4
    cores
    ax-mp
    #
    syl6breq
    wph
    @2
    @9
    @3
    wph
    @2
    @8
    @9
    @6
    @0
    cG
    cdprd
    @18
    oveq2i
    wph
    @7
    @10
    @17
    simprd
    syl5eqr
    wph
    @11
    @12
    @15
    simprd
    eqsstrd
    jca
end
