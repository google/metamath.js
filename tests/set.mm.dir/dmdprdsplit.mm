include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "cres.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "wss.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "simpr.mm"
include "csubg.mm"
include "wf.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "dprdres.mm"
include "simpld.mm"
include "ssun2.mm"
include "jca.mm"
include "c0.mm"
include "dprdcntz2.mm"
include "dprddisj2.mm"
include "3jca.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "simpr2.mm"
include "simpr3.mm"
include "dmdprdsplit2.mm"
include "impbida.mm"

theorem dmdprdsplit
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let cZ: class Z
  let c.po: class .(+)
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume dprdsplit.2: |- ( ph -> S : I --> ( SubGrp ` G ) )
  assume dprdsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume dprdsplit.u: |- ( ph -> I = ( C u. D ) )
  assume dmdprdsplit.z: |- Z = ( Cntz ` G )
  assume dmdprdsplit.0: |- .0. = ( 0g ` G )


  assert |- ( ph -> ( G dom DProd S <-> ( ( G dom DProd ( S |` C ) /\ G dom DProd ( S |` D ) ) /\ ( G DProd ( S |` C ) ) C_ ( Z ` ( G DProd ( S |` D ) ) ) /\ ( ( G DProd ( S |` C ) ) i^i ( G DProd ( S |` D ) ) ) = { .0. } ) ) )

  proof
    wph
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    cG
    cS
    cC
    cres
    #
    @0
    wbr
    #
    cG
    cS
    cD
    cres
    #
    @0
    wbr
    #
    wa
    #
    cG
    @2
    cdprd
    co
    #
    cG
    @4
    cdprd
    co
    #
    cZ
    cfv
    wss
    #
    @7
    @8
    cin
    c.0
    csn
    wceq
    #
    w3a
    #
    wph
    @1
    wa
    #
    @6
    @9
    @10
    @12
    @3
    @5
    @12
    @3
    @7
    cG
    cS
    cdprd
    co
    #
    wss
    @12
    cC
    cS
    cG
    cI
    wph
    @1
    simpr
    #
    wph
    cS
    cdm
    cI
    wceq
    #
    @1
    wph
    cI
    cG
    csubg
    cfv
    #
    cS
    wf
    #
    @15
    dprdsplit.2
    cI
    @16
    cS
    fdm
    syl
    adantr
    #
    @12
    cC
    cD
    cun
    #
    cC
    cI
    cC
    cD
    ssun1
    wph
    cI
    @19
    wceq
    #
    @1
    dprdsplit.u
    adantr
    #
    syl5sseqr
    #
    dprdres
    simpld
    @12
    @5
    @8
    @13
    wss
    @12
    cD
    cS
    cG
    cI
    @14
    @18
    @12
    @19
    cD
    cI
    cD
    cC
    ssun2
    @21
    syl5sseqr
    #
    dprdres
    simpld
    jca
    @12
    cC
    cD
    cS
    cG
    cI
    cZ
    @14
    @18
    @22
    @23
    wph
    cC
    cD
    cin
    c0
    wceq
    #
    @1
    dprdsplit.i
    adantr
    #
    dmdprdsplit.z
    dprdcntz2
    @12
    cC
    cD
    cS
    cG
    cI
    c.0
    @14
    @18
    @22
    @23
    @25
    dmdprdsplit.0
    dprddisj2
    3jca
    wph
    @11
    wa
    cC
    cD
    cS
    cG
    cI
    c.0
    cZ
    wph
    @17
    @11
    dprdsplit.2
    adantr
    wph
    @24
    @11
    dprdsplit.i
    adantr
    wph
    @20
    @11
    dprdsplit.u
    adantr
    dmdprdsplit.z
    dmdprdsplit.0
    @3
    @5
    @9
    @10
    wph
    simpr1l
    @3
    @5
    @9
    @10
    wph
    simpr1r
    wph
    @6
    @9
    @10
    simpr2
    wph
    @6
    @9
    @10
    simpr3
    dmdprdsplit2
    impbida
end
