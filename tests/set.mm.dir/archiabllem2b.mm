include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "archiabllem2c.mm"
include "ctos.mm"
include "wcel.mm"
include "w3o.mm"
include "cogrp.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "3syl.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "tlt3.mm"
include "ecase23d.mm"

theorem archiabllem2b
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let c.x: class .x.
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vc: setvar c
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
  assume archiabllem2b.4: |- ( ph -> X e. B )
  assume archiabllem2b.5: |- ( ph -> Y e. B )

  disjoint a b
  disjoint B a
  disjoint B b
  disjoint W a
  disjoint W b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
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
  disjoint X c
  disjoint X t
  disjoint a m
  disjoint a n
  disjoint b m
  disjoint b n
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
  assert |- ( ph -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cY
    cX
    c.pl
    co
    #
    wceq
    #
    @0
    @1
    c.lt
    wbr
    #
    @1
    @0
    c.lt
    wbr
    #
    wph
    cB
    c.pl
    c.lt
    c.x
    c.le
    cW
    cX
    cY
    c.0
    va
    vb
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    archiabllem.g
    archiabllem.a
    archiabllem2.1
    archiabllem2.2
    archiabllem2.3
    archiabllem2b.4
    archiabllem2b.5
    archiabllem2c
    wph
    cB
    c.pl
    c.lt
    c.x
    c.le
    cW
    cY
    cX
    c.0
    va
    vb
    archiabllem.b
    archiabllem.0
    archiabllem.e
    archiabllem.t
    archiabllem.m
    archiabllem.g
    archiabllem.a
    archiabllem2.1
    archiabllem2.2
    archiabllem2.3
    archiabllem2b.5
    archiabllem2b.4
    archiabllem2c
    wph
    cW
    ctos
    wcel
    #
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @2
    @3
    @4
    w3o
    wph
    cW
    cogrp
    wcel
    #
    cW
    comnd
    wcel
    #
    @5
    archiabllem.g
    @8
    cW
    cgrp
    wcel
    #
    @9
    cW
    isogrp
    simprbi
    cW
    omndtos
    3syl
    wph
    @10
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @6
    wph
    @8
    @10
    archiabllem.g
    cW
    ogrpgrp
    syl
    #
    archiabllem2b.4
    archiabllem2b.5
    cB
    c.pl
    cW
    cX
    cY
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    wph
    @10
    @12
    @11
    @7
    @13
    archiabllem2b.5
    archiabllem2b.4
    cB
    c.pl
    cW
    cY
    cX
    archiabllem.b
    archiabllem2.1
    grpcl
    syl3anc
    cB
    c.lt
    cW
    @0
    @1
    archiabllem.b
    archiabllem.t
    tlt3
    syl3anc
    ecase23d
end
