include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cv.mm"
include "w3a.mm"
include "crn.mm"
include "wrex.mm"
include "wa.mm"
include "wne.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "simplr.mm"
include "simpr.mm"
include "tgelrnln.mm"
include "tglinerflx1.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "eqeltrrd.mm"
include "eqeltrd.mm"
include "eleq2.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tglowdim1i.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "tglinerflx2.mm"
include "pm2.61dane.mm"
include "adantlr.mm"
include "simpll.mm"
include "wn.mm"
include "neneqd.mm"
include "orel2.mm"
include "sylc.mm"
include "syl21anc.mm"
include "df-ne.mm"
include "simplr1.mm"
include "ad3antrrr.mm"
include "simplr2.mm"
include "simplr3.mm"
include "tglinethru.mm"
include "eleqtrd.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"
include "orcomd.mm"
include "r19.29an.mm"
include "impbida.mm"

theorem colline
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume colline.1: |- ( ph -> X e. P )
  assume colline.2: |- ( ph -> Y e. P )
  assume colline.3: |- ( ph -> Z e. P )
  assume colline.4: |- ( ph -> 2 <_ ( # ` P ) )

  disjoint L a
  disjoint X a
  disjoint Y a
  disjoint Z a
  disjoint a ph
  disjoint a x
  disjoint L x
  disjoint P x
  disjoint X x
  disjoint Y x
  disjoint Z x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( X e. ( Y L Z ) \/ Y = Z ) <-> E. a e. ran L ( X e. a /\ Y e. a /\ Z e. a ) ) )

  proof
    wph
    cX
    cY
    cZ
    cL
    co
    #
    wcel
    #
    cY
    cZ
    wceq
    #
    wo
    #
    cX
    va
    cv
    #
    wcel
    #
    cY
    @4
    wcel
    #
    cZ
    @4
    wcel
    #
    w3a
    #
    va
    cL
    crn
    #
    wrex
    #
    wph
    @3
    wa
    #
    @10
    cY
    cZ
    wph
    @2
    @10
    @3
    wph
    @2
    wa
    #
    @10
    cX
    cZ
    @12
    cX
    cZ
    wceq
    #
    wa
    #
    cX
    vx
    cv
    #
    wne
    #
    @10
    vx
    cP
    @14
    @15
    cP
    wcel
    #
    wa
    #
    @16
    wa
    #
    cX
    @15
    cL
    co
    #
    @9
    wcel
    cX
    @20
    wcel
    #
    cY
    @20
    wcel
    #
    cZ
    @20
    wcel
    #
    @10
    @19
    cP
    cG
    cI
    cL
    cX
    @15
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    cG
    cstrkg
    wcel
    #
    @2
    @13
    @17
    @16
    tglineintmo.g
    ad4antr
    #
    wph
    cX
    cP
    wcel
    #
    @2
    @13
    @17
    @16
    colline.1
    ad4antr
    #
    @14
    @17
    @16
    simplr
    #
    @18
    @16
    simpr
    #
    tgelrnln
    @19
    cP
    cX
    @15
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @25
    @27
    @28
    @29
    tglinerflx1
    #
    @19
    cY
    cZ
    @20
    wph
    @2
    @13
    @17
    @16
    simp-4r
    @19
    cX
    cZ
    @20
    @12
    @13
    @17
    @16
    simpllr
    @30
    eqeltrrd
    #
    eqeltrd
    @31
    @8
    @21
    @22
    @23
    w3a
    va
    @20
    @9
    @4
    @20
    wceq
    @5
    @21
    @6
    @22
    @7
    @23
    @4
    @20
    cX
    eleq2
    @4
    @20
    cY
    eleq2
    @4
    @20
    cZ
    eleq2
    3anbi123d
    rspcev
    syl13anc
    wph
    @16
    vx
    cP
    wrex
    @2
    @13
    wph
    vx
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    cX
    tglineintmo.p
    @32
    eqid
    tglineintmo.i
    tglineintmo.g
    colline.4
    colline.1
    tglowdim1i
    ad2antrr
    r19.29a
    @12
    cX
    cZ
    wne
    #
    wa
    #
    cX
    cZ
    cL
    co
    #
    @9
    wcel
    cX
    @35
    wcel
    #
    cY
    @35
    wcel
    #
    cZ
    @35
    wcel
    #
    @10
    @34
    cP
    cG
    cI
    cL
    cX
    cZ
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @24
    @2
    @33
    tglineintmo.g
    ad2antrr
    #
    wph
    @26
    @2
    @33
    colline.1
    ad2antrr
    #
    wph
    cZ
    cP
    wcel
    #
    @2
    @33
    colline.3
    ad2antrr
    #
    @12
    @33
    simpr
    #
    tgelrnln
    @34
    cP
    cX
    cZ
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @39
    @40
    @42
    @43
    tglinerflx1
    @34
    cY
    cZ
    @35
    wph
    @2
    @33
    simplr
    @34
    cP
    cX
    cZ
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @39
    @40
    @42
    @43
    tglinerflx2
    #
    eqeltrd
    @44
    @8
    @36
    @37
    @38
    w3a
    va
    @35
    @9
    @4
    @35
    wceq
    @5
    @36
    @6
    @37
    @7
    @38
    @4
    @35
    cX
    eleq2
    @4
    @35
    cY
    eleq2
    @4
    @35
    cZ
    eleq2
    3anbi123d
    rspcev
    syl13anc
    pm2.61dane
    adantlr
    @11
    cY
    cZ
    wne
    #
    wa
    #
    @0
    @9
    wcel
    #
    @1
    cY
    @0
    wcel
    #
    cZ
    @0
    wcel
    #
    @10
    @46
    wph
    @1
    @45
    @47
    wph
    @3
    @45
    simpll
    #
    @46
    @2
    wn
    #
    @3
    @1
    @46
    cY
    cZ
    @11
    @45
    simpr
    #
    neneqd
    wph
    @3
    @45
    simplr
    @2
    @1
    orel2
    sylc
    #
    @52
    wph
    @1
    wa
    #
    @45
    wa
    #
    cP
    cG
    cI
    cL
    cY
    cZ
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @24
    @1
    @45
    tglineintmo.g
    ad2antrr
    #
    wph
    cY
    cP
    wcel
    #
    @1
    @45
    colline.2
    ad2antrr
    #
    wph
    @41
    @1
    @45
    colline.3
    ad2antrr
    #
    @54
    @45
    simpr
    #
    tgelrnln
    syl21anc
    @53
    @46
    wph
    @1
    @45
    @48
    @50
    @53
    @52
    @55
    cP
    cY
    cZ
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @56
    @58
    @59
    @60
    tglinerflx1
    syl21anc
    @46
    wph
    @1
    @45
    @49
    @50
    @53
    @52
    @55
    cP
    cY
    cZ
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @56
    @58
    @59
    @60
    tglinerflx2
    syl21anc
    @8
    @1
    @48
    @49
    w3a
    va
    @0
    @9
    @4
    @0
    wceq
    @5
    @1
    @6
    @48
    @7
    @49
    @4
    @0
    cX
    eleq2
    @4
    @0
    cY
    eleq2
    @4
    @0
    cZ
    eleq2
    3anbi123d
    rspcev
    syl13anc
    pm2.61dane
    wph
    @8
    @3
    va
    @9
    wph
    @4
    @9
    wcel
    #
    wa
    #
    @8
    wa
    #
    @2
    @1
    @63
    @2
    @1
    @51
    @45
    @63
    @1
    cY
    cZ
    df-ne
    @63
    @45
    @1
    @63
    @45
    wa
    #
    cX
    @4
    @0
    @5
    @6
    @7
    @62
    @45
    simplr1
    @64
    @4
    cP
    cY
    cZ
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @24
    @61
    @8
    @45
    tglineintmo.g
    ad3antrrr
    wph
    @57
    @61
    @8
    @45
    colline.2
    ad3antrrr
    wph
    @41
    @61
    @8
    @45
    colline.3
    ad3antrrr
    @63
    @45
    simpr
    #
    @65
    wph
    @61
    @8
    @45
    simpllr
    @5
    @6
    @7
    @62
    @45
    simplr2
    @5
    @6
    @7
    @62
    @45
    simplr3
    tglinethru
    eleqtrd
    ex
    syl5bir
    orrd
    orcomd
    r19.29an
    impbida
end
