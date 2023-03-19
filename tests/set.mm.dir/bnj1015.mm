include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "c-bnj18.mm"
include "wss.mm"
include "wi.mm"
include "elexi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "bnj1014.mm"
include "vtocl.mm"

theorem bnj1015
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cG: class G
  let cJ: class J
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  assume bnj1015.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1015.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1015.13: |- D = ( _om \ { (/) } )
  assume bnj1015.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1015.15: |- G e. V
  assume bnj1015.16: |- J e. V

  disjoint A f
  disjoint A i
  disjoint f i
  disjoint A n
  disjoint A y
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint i ph
  disjoint A g
  disjoint f g
  disjoint g i
  disjoint A j
  disjoint g j
  disjoint i j
  disjoint B g
  disjoint B j
  disjoint G g
  disjoint G j
  disjoint J j
  disjoint R g
  disjoint R j
  disjoint X g
  disjoint X j
  assert |- ( ( G e. B /\ J e. dom G ) -> ( G ` J ) C_ _trCl ( X , A , R ) )

  proof
    cG
    cB
    wcel
    #
    vj
    cv
    #
    cG
    cdm
    #
    wcel
    #
    wa
    #
    @1
    cG
    cfv
    #
    cA
    cR
    cX
    c-bnj18
    #
    wss
    #
    wi
    #
    @0
    cJ
    @2
    wcel
    #
    wa
    #
    cJ
    cG
    cfv
    #
    @6
    wss
    #
    wi
    vj
    cJ
    cJ
    cV
    bnj1015.16
    elexi
    @1
    cJ
    wceq
    #
    @4
    @10
    @7
    @12
    @13
    @3
    @9
    @0
    @1
    cJ
    @2
    eleq1
    anbi2d
    @13
    @5
    @11
    @6
    @1
    cJ
    cG
    fveq2
    sseq1d
    imbi12d
    vg
    cv
    #
    cB
    wcel
    #
    @1
    @14
    cdm
    #
    wcel
    #
    wa
    #
    @1
    @14
    cfv
    #
    @6
    wss
    #
    wi
    @8
    vg
    cG
    cG
    cV
    bnj1015.15
    elexi
    @14
    cG
    wceq
    #
    @18
    @4
    @20
    @7
    @21
    @15
    @0
    @17
    @3
    @14
    cG
    cB
    eleq1
    @21
    @16
    @2
    @1
    @14
    cG
    dmeq
    eleq2d
    anbi12d
    @21
    @19
    @5
    @6
    @1
    @14
    cG
    fveq1
    sseq1d
    imbi12d
    wph
    wps
    vy
    cA
    cB
    cD
    cR
    vf
    vg
    vi
    vj
    vn
    cX
    bnj1015.1
    bnj1015.2
    bnj1015.13
    bnj1015.14
    bnj1014
    vtocl
    vtocl
end
