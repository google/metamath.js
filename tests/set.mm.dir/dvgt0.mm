include "crp.mm"
include "clt.mm"
include "ltso.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cc0.mm"
include "cmin.mm"
include "cdiv.mm"
include "dvgt0lem1.mm"
include "rpgt0d.mm"
include "cr.mm"
include "wb.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "ffvelrnd.mm"
include "simplrl.mm"
include "resubcld.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "simpr.mm"
include "posdifd.mm"
include "mpbid.mm"
include "gt0div.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "dvgt0lem2.mm"

theorem dvgt0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let cS: class S
  let cX: class X
  let cY: class Y
  assume dvgt0.a: |- ( ph -> A e. RR )
  assume dvgt0.b: |- ( ph -> B e. RR )
  assume dvgt0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvgt0.d: |- ( ph -> ( RR _D F ) : ( A (,) B ) --> RR+ )


  assert |- ( ph -> F Isom < , < ( ( A [,] B ) , ran F ) )

  proof
    wph
    vx
    vy
    cA
    cB
    crp
    cF
    clt
    dvgt0.a
    dvgt0.b
    dvgt0.f
    dvgt0.d
    ltso
    wph
    vx
    cv
    #
    cA
    cB
    cicc
    co
    #
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    wa
    #
    @0
    @3
    clt
    wbr
    #
    wa
    #
    @0
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    clt
    wbr
    cc0
    @10
    @9
    cmin
    co
    #
    clt
    wbr
    #
    @8
    @12
    cc0
    @11
    @3
    @0
    cmin
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    @8
    @14
    wph
    cA
    cB
    crp
    cF
    @0
    @3
    dvgt0.a
    dvgt0.b
    dvgt0.f
    dvgt0.d
    dvgt0lem1
    rpgt0d
    @8
    @11
    cr
    wcel
    @13
    cr
    wcel
    cc0
    @13
    clt
    wbr
    #
    @12
    @15
    wb
    @8
    @10
    @9
    @8
    @1
    cr
    @3
    cF
    wph
    @1
    cr
    cF
    wf
    #
    @5
    @7
    wph
    cF
    @1
    cr
    ccncf
    co
    wcel
    @17
    dvgt0.f
    @1
    cr
    cF
    cncff
    syl
    ad2antrr
    #
    wph
    @2
    @4
    @7
    simplrr
    #
    ffvelrnd
    #
    @8
    @1
    cr
    @0
    cF
    @18
    wph
    @2
    @4
    @7
    simplrl
    #
    ffvelrnd
    #
    resubcld
    @8
    @3
    @0
    @8
    @1
    cr
    @3
    wph
    @1
    cr
    wss
    #
    @5
    @7
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @23
    dvgt0.a
    dvgt0.b
    cA
    cB
    iccssre
    syl2anc
    ad2antrr
    #
    @19
    sseldd
    #
    @8
    @1
    cr
    @0
    @24
    @21
    sseldd
    #
    resubcld
    @8
    @7
    @16
    @6
    @7
    simpr
    @8
    @0
    @3
    @26
    @25
    posdifd
    mpbid
    @11
    @13
    gt0div
    syl3anc
    mpbird
    @8
    @9
    @10
    @22
    @20
    posdifd
    mpbird
    dvgt0lem2
end
