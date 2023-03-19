include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cvv.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "ovexd.mm"
include "fveq2.mm"
include "oveq1.mm"
include "cbs.mm"
include "wf.mm"
include "wfun.mm"
include "cygznlem2a.mm"
include "ffun.mm"
include "syl.mm"
include "fliftval.mm"

theorem cygznlem2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume cygzn.b: |- B = ( Base ` G )
  assume cygzn.n: |- N = if ( B e. Fin , ( # ` B ) , 0 )
  assume cygzn.y: |- Y = ( Z/nZ ` N )
  assume cygzn.m: |- .x. = ( .g ` G )
  assume cygzn.l: |- L = ( ZRHom ` Y )
  assume cygzn.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cygzn.g: |- ( ph -> G e. CycGrp )
  assume cygzn.x: |- ( ph -> X e. E )
  assume cygzn.f: |- F = ran ( m e. ZZ |-> <. ( L ` m ) , ( m .x. X ) >. )

  disjoint m n
  disjoint m x
  disjoint B m
  disjoint n x
  disjoint B n
  disjoint B x
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint M m
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint L m
  disjoint L n
  disjoint L x
  disjoint N x
  disjoint m ph
  disjoint F n
  disjoint F x
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a z
  disjoint B a
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b z
  disjoint B b
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g z
  disjoint B g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint B i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j z
  disjoint B j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint B k
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint B z
  disjoint E z
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G z
  disjoint .x. a
  disjoint .x. j
  disjoint .x. k
  disjoint .x. z
  disjoint Y a
  disjoint Y b
  disjoint Y g
  disjoint Y i
  disjoint Y j
  disjoint Y z
  disjoint L a
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint F a
  disjoint F b
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F z
  disjoint X a
  disjoint X j
  disjoint X k
  disjoint X z
  assert |- ( ( ph /\ M e. ZZ ) -> ( F ` ( L ` M ) ) = ( M .x. X ) )

  proof
    wph
    vm
    vm
    cv
    #
    cL
    cfv
    @0
    cX
    c.x
    co
    cM
    cL
    cfv
    cM
    cX
    c.x
    co
    cvv
    cvv
    cF
    cz
    cM
    cygzn.f
    wph
    @0
    cz
    wcel
    wa
    #
    @0
    cL
    fvexd
    @1
    @0
    cX
    c.x
    ovexd
    @0
    cM
    cL
    fveq2
    @0
    cM
    cX
    c.x
    oveq1
    wph
    cY
    cbs
    cfv
    #
    cB
    cF
    wf
    cF
    wfun
    wph
    vx
    cB
    c.x
    vm
    vn
    cE
    cF
    cG
    cL
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygzn.f
    cygznlem2a
    @2
    cB
    cF
    ffun
    syl
    fliftval
end
