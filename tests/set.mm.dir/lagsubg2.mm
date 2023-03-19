include "chash.mm"
include "cfv.mm"
include "cqs.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "co.mm"
include "csubg.mm"
include "wcel.mm"
include "wer.mm"
include "eqger.mm"
include "syl.mm"
include "qshash.mm"
include "wa.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "eqgen.mm"
include "sylan.mm"
include "cfn.mm"
include "wb.mm"
include "wss.mm"
include "subgss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cpw.mm"
include "qsss.mm"
include "sselda.mm"
include "elpwid.mm"
include "hashen.mm"
include "mpbird.mm"
include "sumeq2dv.mm"
include "cc.mm"
include "pwfi.mm"
include "sylib.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "fsumconst.mm"
include "3eqtr2d.mm"

theorem lagsubg2
  let wph: wff ph
  let c.sm: class .~
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume lagsubg.1: |- X = ( Base ` G )
  assume lagsubg.2: |- .~ = ( G ~QG Y )
  assume lagsubg.3: |- ( ph -> Y e. ( SubGrp ` G ) )
  assume lagsubg.4: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( # ` X ) = ( ( # ` ( X /. .~ ) ) x. ( # ` Y ) ) )

  proof
    wph
    cX
    chash
    cfv
    cX
    c.sm
    cqs
    #
    vx
    cv
    #
    chash
    cfv
    #
    vx
    csu
    @0
    cY
    chash
    cfv
    #
    vx
    csu
    #
    @0
    chash
    cfv
    @3
    cmul
    co
    #
    wph
    vx
    cX
    c.sm
    wph
    cY
    cG
    csubg
    cfv
    wcel
    #
    cX
    c.sm
    wer
    lagsubg.3
    c.sm
    cG
    cX
    cY
    lagsubg.1
    lagsubg.2
    eqger
    syl
    #
    lagsubg.4
    qshash
    wph
    @0
    @3
    @2
    vx
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    @2
    wceq
    #
    cY
    @1
    cen
    wbr
    #
    wph
    @6
    @8
    @11
    lagsubg.3
    @1
    c.sm
    cG
    cX
    cY
    lagsubg.1
    lagsubg.2
    eqgen
    sylan
    @9
    cY
    cfn
    wcel
    #
    @1
    cfn
    wcel
    #
    @10
    @11
    wb
    wph
    @12
    @8
    wph
    cX
    cfn
    wcel
    #
    cY
    cX
    wss
    #
    @12
    lagsubg.4
    wph
    @6
    @15
    lagsubg.3
    cX
    cY
    cG
    lagsubg.1
    subgss
    syl
    cX
    cY
    ssfi
    syl2anc
    #
    adantr
    @9
    @14
    @1
    cX
    wss
    @13
    wph
    @14
    @8
    lagsubg.4
    adantr
    @9
    @1
    cX
    wph
    @0
    cX
    cpw
    #
    @1
    wph
    cX
    c.sm
    @7
    qsss
    #
    sselda
    elpwid
    cX
    @1
    ssfi
    syl2anc
    cY
    @1
    hashen
    syl2anc
    mpbird
    sumeq2dv
    wph
    @0
    cfn
    wcel
    #
    @3
    cc
    wcel
    @4
    @5
    wceq
    wph
    @17
    cfn
    wcel
    #
    @0
    @17
    wss
    @19
    wph
    @14
    @20
    lagsubg.4
    cX
    pwfi
    sylib
    @18
    @17
    @0
    ssfi
    syl2anc
    wph
    @3
    wph
    @12
    @3
    cn0
    wcel
    @16
    cY
    hashcl
    syl
    nn0cnd
    @0
    @3
    vx
    fsumconst
    syl2anc
    3eqtr2d
end
