include "co.mm"
include "wbr.mm"
include "chom.mm"
include "cfv.mm"
include "wcel.mm"
include "cop.mm"
include "cco.mm"
include "ccid.mm"
include "wceq.mm"
include "w3a.mm"
include "wf.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "eqid.mm"
include "ccat.mm"
include "setccat.mm"
include "syl.mm"
include "setcbas.mm"
include "eleqtrd.mm"
include "issect.mm"
include "wa.mm"
include "elsetchom.mm"
include "anbi12d.mm"
include "anbi1d.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "setcco.mm"
include "setcid.mm"
include "eqeq12d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "df-3an.mm"
include "3bitr4g.mm"

theorem setcsect
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cE: class E
  let vx: setvar x
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume setcmon.c: |- C = ( SetCat ` U )
  assume setcmon.u: |- ( ph -> U e. V )
  assume setcmon.x: |- ( ph -> X e. U )
  assume setcmon.y: |- ( ph -> Y e. U )
  assume setcsect.n: |- S = ( Sect ` C )


  assert |- ( ph -> ( F ( X S Y ) G <-> ( F : X --> Y /\ G : Y --> X /\ ( G o. F ) = ( _I |` X ) ) ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    cF
    cX
    cY
    cC
    chom
    cfv
    #
    co
    wcel
    #
    cG
    cY
    cX
    @0
    co
    wcel
    #
    cG
    cF
    cX
    cY
    cop
    cX
    cC
    cco
    cfv
    #
    co
    co
    #
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    w3a
    #
    cX
    cY
    cF
    wf
    #
    cY
    cX
    cG
    wf
    #
    cG
    cF
    ccom
    #
    cid
    cX
    cres
    #
    wceq
    #
    w3a
    #
    wph
    cC
    cbs
    cfv
    #
    cC
    cS
    @3
    @5
    cF
    cG
    @0
    cX
    cY
    @15
    eqid
    @0
    eqid
    #
    @3
    eqid
    #
    @5
    eqid
    #
    setcsect.n
    wph
    cU
    cV
    wcel
    #
    cC
    ccat
    wcel
    setcmon.u
    cC
    cU
    cV
    setcmon.c
    setccat
    syl
    wph
    cX
    cU
    @15
    setcmon.x
    wph
    cC
    cU
    cV
    setcmon.c
    setcmon.u
    setcbas
    #
    eleqtrd
    wph
    cY
    cU
    @15
    setcmon.y
    @20
    eleqtrd
    issect
    wph
    @1
    @2
    wa
    #
    @7
    wa
    #
    @9
    @10
    wa
    #
    @13
    wa
    #
    @8
    @14
    wph
    @22
    @23
    @7
    wa
    @24
    wph
    @21
    @23
    @7
    wph
    @1
    @9
    @2
    @10
    wph
    cC
    cU
    cF
    @0
    cV
    cX
    cY
    setcmon.c
    setcmon.u
    @16
    setcmon.x
    setcmon.y
    elsetchom
    wph
    cC
    cU
    cG
    @0
    cV
    cY
    cX
    setcmon.c
    setcmon.u
    @16
    setcmon.y
    setcmon.x
    elsetchom
    anbi12d
    anbi1d
    wph
    @23
    @7
    @13
    wph
    @23
    wa
    #
    @4
    @11
    @6
    @12
    @25
    cC
    @3
    cU
    cF
    cG
    cV
    cX
    cY
    cX
    setcmon.c
    wph
    @19
    @23
    setcmon.u
    adantr
    @17
    wph
    cX
    cU
    wcel
    @23
    setcmon.x
    adantr
    #
    wph
    cY
    cU
    wcel
    @23
    setcmon.y
    adantr
    @26
    wph
    @9
    @10
    simprl
    wph
    @9
    @10
    simprr
    setcco
    wph
    @6
    @12
    wceq
    @23
    wph
    cC
    cU
    @5
    cV
    cX
    setcmon.c
    @18
    setcmon.u
    setcmon.x
    setcid
    adantr
    eqeq12d
    pm5.32da
    bitrd
    @1
    @2
    @7
    df-3an
    @9
    @10
    @13
    df-3an
    3bitr4g
    bitrd
end
