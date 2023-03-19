include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cabl.mm"
include "cogrp.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "carchi.mm"
include "coppg.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "simp1.mm"
include "syl3an1.mm"
include "simp2.mm"
include "simp3.mm"
include "archiabllem2b.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "isabl2.mm"
include "sylanbrc.mm"

theorem archiabllem2
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let c.x: class .x.
  let c.le: class .<_
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vc: setvar c
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  assume archiabllem.b: |- B = ( Base ` W )
  assume archiabllem.0: |- .0. = ( 0g ` W )
  assume archiabllem.e: |- .<_ = ( le ` W )
  assume archiabllem.t: |- .< = ( lt ` W )
  assume archiabllem.m: |- .x. = ( .g ` W )
  assume archiabllem.g: |- ( ph -> W e. oGrp )
  assume archiabllem.a: |- ( ph -> W e. Archi )
  assume archiabllem2.1: |- .+ = ( +g ` W )
  assume archiabllem2.2: |- ( ph -> ( oppG ` W ) e. oGrp )
  assume archiabllem2.3: |- ( ( ph /\ a e. B /\ .0. .< a ) -> E. b e. B ( .0. .< b /\ b .< a ) )

  disjoint a b
  disjoint B a
  disjoint B b
  disjoint W a
  disjoint W b
  disjoint a ph
  disjoint b ph
  disjoint .+ a
  disjoint .+ b
  disjoint .<_ a
  disjoint .<_ b
  disjoint .< a
  disjoint .< b
  disjoint .0. a
  disjoint .0. b
  disjoint a b
  disjoint m n
  disjoint m t
  disjoint n t
  disjoint a c
  disjoint a t
  disjoint b c
  disjoint b t
  disjoint c t
  disjoint B c
  disjoint B t
  disjoint W c
  disjoint W t
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X t
  disjoint a m
  disjoint a n
  disjoint Y a
  disjoint b m
  disjoint b n
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint Y t
  disjoint ph t
  disjoint c m
  disjoint c n
  disjoint .+ c
  disjoint .+ t
  disjoint .+ m
  disjoint .+ n
  disjoint .<_ c
  disjoint .<_ t
  disjoint .<_ m
  disjoint .<_ n
  disjoint .< c
  disjoint .< t
  disjoint .< m
  disjoint .< n
  disjoint .0. c
  disjoint .0. t
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint U m
  disjoint U n
  disjoint U x
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint .0. m
  disjoint .0. n
  disjoint .0. x
  disjoint .< m
  disjoint .< n
  disjoint .< x
  disjoint .<_ m
  disjoint .<_ x
  assert |- ( ph -> W e. Abel )

  proof
    wph
    cW
    cgrp
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @2
    @1
    c.pl
    co
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cW
    cabl
    wcel
    wph
    cW
    cogrp
    wcel
    #
    @0
    archiabllem.g
    cW
    ogrpgrp
    syl
    wph
    @3
    vx
    vy
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @3
    wph
    @5
    @6
    w3a
    #
    cB
    c.pl
    c.lt
    c.x
    c.le
    cW
    @1
    @2
    c.0
    va
    vb
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    wph
    @5
    @4
    @6
    archiabllem.g
    3ad2ant1
    wph
    @5
    cW
    carchi
    wcel
    @6
    archiabllem.a
    3ad2ant1
    archiabllem2.1
    wph
    @5
    cW
    coppg
    cfv
    cogrp
    wcel
    @6
    archiabllem2.2
    3ad2ant1
    @7
    wph
    va
    cv
    #
    cB
    wcel
    c.0
    @8
    c.lt
    wbr
    c.0
    vb
    cv
    #
    c.lt
    wbr
    @9
    @8
    c.lt
    wbr
    wa
    vb
    cB
    wrex
    wph
    @5
    @6
    simp1
    archiabllem2.3
    syl3an1
    wph
    @5
    @6
    simp2
    wph
    @5
    @6
    simp3
    archiabllem2b
    3expb
    ralrimivva
    vx
    vy
    cB
    c.pl
    cW
    archiabllem.b
    archiabllem2.1
    isabl2
    sylanbrc
end
