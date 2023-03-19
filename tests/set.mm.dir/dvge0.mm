include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "cle.mm"
include "wceq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "cdiv.mm"
include "cpnf.mm"
include "cico.mm"
include "wcel.mm"
include "cicc.mm"
include "wi.mm"
include "dvgt0lem1.mm"
include "exp31.mm"
include "mp2and.mm"
include "imp.mm"
include "cr.mm"
include "elrege0.mm"
include "simprbi.mm"
include "syl.mm"
include "wb.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "adantr.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "posdifd.mm"
include "biimpa.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "ex.mm"
include "subge0d.mm"
include "sylibd.mm"
include "leidd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "leloed.mm"
include "mpbid.mm"
include "mpjaod.mm"

theorem dvge0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let cS: class S
  assume dvgt0.a: |- ( ph -> A e. RR )
  assume dvgt0.b: |- ( ph -> B e. RR )
  assume dvgt0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvge0.d: |- ( ph -> ( RR _D F ) : ( A (,) B ) --> ( 0 [,) +oo ) )
  assume dvge0.x: |- ( ph -> X e. ( A [,] B ) )
  assume dvge0.y: |- ( ph -> Y e. ( A [,] B ) )
  assume dvge0.l: |- ( ph -> X <_ Y )


  assert |- ( ph -> ( F ` X ) <_ ( F ` Y ) )

  proof
    wph
    cX
    cY
    clt
    wbr
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cle
    wbr
    #
    cX
    cY
    wceq
    #
    wph
    @0
    cc0
    @2
    @1
    cmin
    co
    #
    cle
    wbr
    #
    @3
    wph
    @0
    @6
    wph
    @0
    wa
    #
    @6
    cc0
    @5
    cY
    cX
    cmin
    co
    #
    cdiv
    co
    #
    cle
    wbr
    #
    @7
    @9
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @10
    wph
    @0
    @12
    wph
    cX
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cY
    @13
    wcel
    #
    @0
    @12
    wi
    dvge0.x
    dvge0.y
    wph
    @14
    @15
    wa
    @0
    @12
    wph
    cA
    cB
    @11
    cF
    cX
    cY
    dvgt0.a
    dvgt0.b
    dvgt0.f
    dvge0.d
    dvgt0lem1
    exp31
    mp2and
    imp
    @12
    @9
    cr
    wcel
    @10
    @9
    elrege0
    simprbi
    syl
    @7
    @5
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    @6
    @10
    wb
    wph
    @16
    @0
    wph
    @2
    @1
    wph
    @13
    cr
    cY
    cF
    wph
    cF
    @13
    cr
    ccncf
    co
    wcel
    @13
    cr
    cF
    wf
    dvgt0.f
    @13
    cr
    cF
    cncff
    syl
    #
    dvge0.y
    ffvelrnd
    #
    wph
    @13
    cr
    cX
    cF
    @19
    dvge0.x
    ffvelrnd
    #
    resubcld
    adantr
    wph
    @17
    @0
    wph
    cY
    cX
    wph
    @13
    cr
    cY
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @13
    cr
    wss
    dvgt0.a
    dvgt0.b
    cA
    cB
    iccssre
    syl2anc
    #
    dvge0.y
    sseldd
    #
    wph
    @13
    cr
    cX
    @22
    dvge0.x
    sseldd
    #
    resubcld
    adantr
    wph
    @0
    @18
    wph
    cX
    cY
    @24
    @23
    posdifd
    biimpa
    @5
    @8
    ge0div
    syl3anc
    mpbird
    ex
    wph
    @2
    @1
    @20
    @21
    subge0d
    sylibd
    wph
    @3
    @4
    @2
    @2
    cle
    wbr
    wph
    @2
    @20
    leidd
    @4
    @1
    @2
    @2
    cle
    cX
    cY
    cF
    fveq2
    breq1d
    syl5ibrcom
    wph
    cX
    cY
    cle
    wbr
    @0
    @4
    wo
    dvge0.l
    wph
    cX
    cY
    @24
    @23
    leloed
    mpbid
    mpjaod
end
