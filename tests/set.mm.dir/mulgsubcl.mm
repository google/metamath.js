include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cn0.mm"
include "co.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "mulgnn0subcl.mm"
include "3expa.mm"
include "an32s.mm"
include "3adantl2.mm"
include "cfv.mm"
include "simp2.mm"
include "adantr.mm"
include "zcnd.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "id.mm"
include "wss.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "sseldd.mm"
include "mulgnegnn.mm"
include "syl2anr.mm"
include "eqtr3d.mm"
include "cv.mm"
include "wral.mm"
include "mulgnnsubcl.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "adantrl.mm"
include "wo.mm"
include "elznn0nn.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem mulgsubcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume mulgnnsubcl.b: |- B = ( Base ` G )
  assume mulgnnsubcl.t: |- .x. = ( .g ` G )
  assume mulgnnsubcl.p: |- .+ = ( +g ` G )
  assume mulgnnsubcl.g: |- ( ph -> G e. V )
  assume mulgnnsubcl.s: |- ( ph -> S C_ B )
  assume mulgnnsubcl.c: |- ( ( ph /\ x e. S /\ y e. S ) -> ( x .+ y ) e. S )
  assume mulgnn0subcl.z: |- .0. = ( 0g ` G )
  assume mulgnn0subcl.c: |- ( ph -> .0. e. S )
  assume mulgsubcl.i: |- I = ( invg ` G )
  assume mulgsubcl.c: |- ( ( ph /\ x e. S ) -> ( I ` x ) e. S )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint .x. x
  disjoint X x
  disjoint X y
  assert |- ( ( ph /\ N e. ZZ /\ X e. S ) -> ( N .x. X ) e. S )

  proof
    wph
    cN
    cz
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cN
    cn0
    wcel
    #
    cN
    cX
    c.x
    co
    #
    cS
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wph
    @1
    @3
    @5
    @0
    wph
    @3
    @1
    @5
    wph
    @3
    @1
    @5
    wph
    vx
    vy
    cB
    c.pl
    cS
    c.x
    cG
    cN
    cV
    cX
    c.0
    mulgnnsubcl.b
    mulgnnsubcl.t
    mulgnnsubcl.p
    mulgnnsubcl.g
    mulgnnsubcl.s
    mulgnnsubcl.c
    mulgnn0subcl.z
    mulgnn0subcl.c
    mulgnn0subcl
    3expa
    an32s
    3adantl2
    @2
    @8
    @5
    @6
    @2
    @8
    wa
    #
    @4
    @7
    cX
    c.x
    co
    #
    cI
    cfv
    #
    cS
    @10
    @7
    cneg
    #
    cX
    c.x
    co
    #
    @4
    @12
    @10
    @13
    cN
    cX
    c.x
    @10
    cN
    @10
    cN
    @2
    @0
    @8
    wph
    @0
    @1
    simp2
    #
    adantr
    zcnd
    negnegd
    oveq1d
    @8
    @8
    cX
    cB
    wcel
    @14
    @12
    wceq
    @2
    @8
    id
    @2
    cS
    cB
    cX
    wph
    @0
    cS
    cB
    wss
    @1
    mulgnnsubcl.s
    3ad2ant1
    wph
    @0
    @1
    simp3
    sseldd
    cB
    c.x
    cG
    cI
    @7
    cX
    mulgnnsubcl.b
    mulgnnsubcl.t
    mulgsubcl.i
    mulgnegnn
    syl2anr
    eqtr3d
    @10
    @11
    cS
    wcel
    #
    vx
    cv
    #
    cI
    cfv
    #
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @12
    cS
    wcel
    #
    wph
    @1
    @8
    @16
    @0
    wph
    @8
    @1
    @16
    wph
    @8
    @1
    @16
    wph
    vx
    vy
    cB
    c.pl
    cS
    c.x
    cG
    @7
    cV
    cX
    mulgnnsubcl.b
    mulgnnsubcl.t
    mulgnnsubcl.p
    mulgnnsubcl.g
    mulgnnsubcl.s
    mulgnnsubcl.c
    mulgnnsubcl
    3expa
    an32s
    3adantl2
    @2
    @20
    @8
    wph
    @0
    @20
    @1
    wph
    @19
    vx
    cS
    mulgsubcl.c
    ralrimiva
    3ad2ant1
    adantr
    @19
    @21
    vx
    @11
    cS
    @17
    @11
    wceq
    @18
    @12
    cS
    @17
    @11
    cI
    fveq2
    eleq1d
    rspcv
    sylc
    eqeltrd
    adantrl
    @2
    @0
    @3
    @9
    wo
    @15
    cN
    elznn0nn
    sylib
    mpjaodan
end
