include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ssid.mm"
include "jctil.mm"
include "wceq.mm"
include "sseq2.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"

theorem lbsextlem1
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vs: setvar s
  let vt: setvar t
  let cT: class T
  let cA: class A
  assume lbsext.v: |- V = ( Base ` W )
  assume lbsext.j: |- J = ( LBasis ` W )
  assume lbsext.n: |- N = ( LSpan ` W )
  assume lbsext.w: |- ( ph -> W e. LVec )
  assume lbsext.c: |- ( ph -> C C_ V )
  assume lbsext.x: |- ( ph -> A. x e. C -. x e. ( N ` ( C \ { x } ) ) )
  assume lbsext.s: |- S = { z e. ~P V | ( C C_ z /\ A. x e. z -. x e. ( N ` ( z \ { x } ) ) ) }

  disjoint J x
  disjoint ph x
  disjoint S x
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint N x
  disjoint N z
  disjoint V x
  disjoint V z
  disjoint W x
  disjoint m n
  disjoint m r
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m ph
  disjoint n r
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n ph
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint ph r
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph y
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint S s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint S u
  disjoint S w
  disjoint S y
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T v
  disjoint T w
  disjoint m z
  disjoint N m
  disjoint n z
  disjoint N n
  disjoint u z
  disjoint N u
  disjoint w z
  disjoint N w
  disjoint y z
  disjoint N y
  disjoint V u
  disjoint V w
  disjoint W m
  disjoint W n
  disjoint W r
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint m s
  disjoint m t
  disjoint A m
  disjoint n s
  disjoint n t
  disjoint A n
  disjoint s z
  disjoint A s
  disjoint t z
  disjoint A t
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( ph -> S =/= (/) )

  proof
    wph
    cC
    cS
    wcel
    #
    cS
    c0
    wne
    wph
    cC
    cV
    cpw
    #
    wcel
    #
    cC
    cC
    wss
    #
    vx
    cv
    #
    cC
    @4
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cC
    wral
    #
    wa
    #
    @0
    wph
    cC
    cV
    wss
    @2
    lbsext.c
    cC
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lbsext.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    sylibr
    wph
    @10
    @3
    lbsext.x
    cC
    ssid
    jctil
    cC
    vz
    cv
    #
    wss
    #
    @4
    @12
    @5
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @12
    wral
    #
    wa
    @11
    vz
    cC
    @1
    cS
    @12
    cC
    wceq
    #
    @13
    @3
    @18
    @10
    @12
    cC
    cC
    sseq2
    @17
    @9
    vx
    @12
    cC
    @19
    @16
    @8
    @19
    @15
    @7
    @4
    @19
    @14
    @6
    cN
    @12
    cC
    @5
    difeq1
    fveq2d
    eleq2d
    notbid
    raleqbi1dv
    anbi12d
    lbsext.s
    elrab2
    sylanbrc
    cS
    cC
    ne0i
    syl
end
