include "cc.mm"
include "wss.mm"
include "wf.mm"
include "wa.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cnt.mm"
include "cfv.mm"
include "reldv.mm"
include "relres.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "cin.mm"
include "simpll.mm"
include "simplr.mm"
include "inss1.mm"
include "fssres.mm"
include "sylancl.mm"
include "resres.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "simprl.mm"
include "syl5ss.mm"
include "dvcl.mm"
include "ex.mm"
include "adantrd.mm"
include "wb.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "eqid.mm"
include "adantr.mm"
include "simplrr.mm"
include "simpr.mm"
include "dvreslem.mm"
include "pm5.21ndd.mm"
include "vex.mm"
include "brres.mm"
include "syl6bbr.mm"
include "eqbrrdiv.mm"

theorem dvres
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  assume dvres.k: |- K = ( TopOpen ` CCfld )
  assume dvres.t: |- T = ( K |`t S )


  assert |- ( ( ( S C_ CC /\ F : A --> CC ) /\ ( A C_ S /\ B C_ S ) ) -> ( S _D ( F |` B ) ) = ( ( S _D F ) |` ( ( int ` T ) ` B ) ) )

  proof
    cS
    cc
    wss
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    cA
    cS
    wss
    #
    cB
    cS
    wss
    #
    wa
    #
    wa
    #
    vx
    vy
    cS
    cF
    cB
    cres
    #
    cdv
    co
    #
    cS
    cF
    cdv
    co
    #
    cB
    cT
    cnt
    cfv
    cfv
    #
    cres
    #
    cS
    @7
    reldv
    @9
    @10
    relres
    @6
    vx
    cv
    #
    vy
    cv
    #
    @8
    wbr
    #
    @12
    @13
    @9
    wbr
    #
    @12
    @10
    wcel
    #
    wa
    #
    @12
    @13
    @11
    wbr
    @6
    @13
    cc
    wcel
    #
    @14
    @17
    @6
    @14
    @18
    @6
    cA
    cB
    cin
    #
    @12
    @13
    cS
    @7
    @0
    @1
    @5
    simpll
    #
    @6
    @19
    cc
    cF
    @19
    cres
    #
    wf
    #
    @19
    cc
    @7
    wf
    @6
    @1
    @19
    cA
    wss
    @22
    @0
    @1
    @5
    simplr
    #
    cA
    cB
    inss1
    #
    cA
    cc
    @19
    cF
    fssres
    sylancl
    @6
    @19
    cc
    @21
    @7
    @6
    @21
    cF
    cA
    cres
    #
    cB
    cres
    @7
    cF
    cA
    cB
    resres
    @6
    @25
    cF
    cB
    @6
    @1
    cF
    cA
    wfn
    @25
    cF
    wceq
    @23
    cA
    cc
    cF
    ffn
    cA
    cF
    fnresdm
    3syl
    reseq1d
    syl5eqr
    feq1d
    mpbid
    @6
    @19
    cA
    cS
    @24
    @2
    @3
    @4
    simprl
    #
    syl5ss
    dvcl
    ex
    @6
    @15
    @18
    @16
    @6
    @15
    @18
    @6
    cA
    @12
    @13
    cS
    cF
    @20
    @23
    @26
    dvcl
    ex
    adantrd
    @6
    @18
    @14
    @17
    wb
    @6
    @18
    wa
    vx
    vy
    vz
    cA
    cB
    cS
    cT
    cF
    vz
    cA
    @12
    csn
    cdif
    vz
    cv
    #
    cF
    cfv
    @12
    cF
    cfv
    cmin
    co
    @27
    @12
    cmin
    co
    cdiv
    co
    cmpt
    #
    cK
    dvres.k
    dvres.t
    @28
    eqid
    @6
    @0
    @18
    @20
    adantr
    @6
    @1
    @18
    @23
    adantr
    @6
    @3
    @18
    @26
    adantr
    @2
    @3
    @4
    @18
    simplrr
    @6
    @18
    simpr
    dvreslem
    ex
    pm5.21ndd
    @12
    @13
    @9
    @10
    vy
    vex
    brres
    syl6bbr
    eqbrrdiv
end
