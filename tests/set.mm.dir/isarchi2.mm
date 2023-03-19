include "ctos.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "carchi.mm"
include "cv.mm"
include "cinftm.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "co.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "wb.mm"
include "eqid.mm"
include "isarchi.mm"
include "adantr.mm"
include "w3a.mm"
include "simpl1l.mm"
include "cn0.mm"
include "simpl1r.mm"
include "simpr.mm"
include "nnnn0d.mm"
include "simpl2.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "tltnle.mm"
include "con2bid.mm"
include "rexbidva.mm"
include "imbi2d.mm"
include "isinftm.mm"
include "notbid.mm"
include "rexnal.mm"
include "imbi2i.mm"
include "imnan.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "3adant1r.mm"
include "bitr4d.mm"
include "3expb.mm"
include "2ralbidva.mm"

theorem isarchi2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let vn: setvar n
  let c.le: class .<_
  let cW: class W
  let c.0: class .0.
  assume isarchi2.b: |- B = ( Base ` W )
  assume isarchi2.0: |- .0. = ( 0g ` W )
  assume isarchi2.x: |- .x. = ( .g ` W )
  assume isarchi2.l: |- .<_ = ( le ` W )
  assume isarchi2.t: |- .< = ( lt ` W )

  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint W n
  disjoint W x
  disjoint W y
  assert |- ( ( W e. Toset /\ W e. Mnd ) -> ( W e. Archi <-> A. x e. B A. y e. B ( .0. .< x -> E. n e. NN y .<_ ( n .x. x ) ) ) )

  proof
    cW
    ctos
    wcel
    #
    cW
    cmnd
    wcel
    #
    wa
    #
    cW
    carchi
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cinftm
    cfv
    #
    wbr
    #
    wn
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    c.0
    @4
    c.lt
    wbr
    #
    @5
    vn
    cv
    #
    @4
    c.x
    co
    #
    c.le
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @0
    @3
    @9
    wb
    @1
    vx
    vy
    cB
    @6
    ctos
    cW
    c.0
    isarchi2.b
    isarchi2.0
    @6
    eqid
    isarchi
    adantr
    @2
    @15
    @8
    vx
    vy
    cB
    cB
    @2
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @15
    @8
    wb
    @2
    @16
    @17
    w3a
    #
    @15
    @10
    @12
    @5
    c.lt
    wbr
    #
    wn
    #
    vn
    cn
    wrex
    #
    wi
    #
    @8
    @18
    @14
    @21
    @10
    @18
    @13
    @20
    vn
    cn
    @18
    @11
    cn
    wcel
    #
    wa
    #
    @0
    @12
    cB
    wcel
    #
    @17
    @13
    @20
    wb
    @0
    @1
    @16
    @17
    @23
    simpl1l
    @24
    @1
    @11
    cn0
    wcel
    @16
    @25
    @0
    @1
    @16
    @17
    @23
    simpl1r
    @24
    @11
    @18
    @23
    simpr
    nnnn0d
    @2
    @16
    @17
    @23
    simpl2
    cB
    c.x
    cW
    @11
    @4
    isarchi2.b
    isarchi2.x
    mulgnn0cl
    syl3anc
    @2
    @16
    @17
    @23
    simpl3
    @0
    @25
    @17
    w3a
    @19
    @13
    cB
    c.lt
    cW
    c.le
    @12
    @5
    isarchi2.b
    isarchi2.l
    isarchi2.t
    tltnle
    con2bid
    syl3anc
    rexbidva
    imbi2d
    @0
    @16
    @17
    @8
    @22
    wb
    @1
    @0
    @16
    @17
    w3a
    #
    @8
    @10
    @19
    vn
    cn
    wral
    #
    wa
    #
    wn
    #
    @22
    @26
    @7
    @28
    cB
    c.lt
    c.x
    vn
    ctos
    cW
    @4
    @5
    c.0
    isarchi2.b
    isarchi2.0
    isarchi2.x
    isarchi2.t
    isinftm
    notbid
    @22
    @10
    @27
    wn
    #
    wi
    @29
    @21
    @30
    @10
    @19
    vn
    cn
    rexnal
    imbi2i
    @10
    @27
    imnan
    bitr2i
    syl6bb
    3adant1r
    bitr4d
    3expb
    2ralbidva
    bitr4d
end
