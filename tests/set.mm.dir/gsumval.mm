include "cvv.mm"
include "wf.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "gsumvalx.mm"

theorem gsumval
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vs: setvar s
  let vg: setvar g
  let vo: setvar o
  let vw: setvar w
  let vy: setvar y
  assume gsumval.b: |- B = ( Base ` G )
  assume gsumval.z: |- .0. = ( 0g ` G )
  assume gsumval.p: |- .+ = ( +g ` G )
  assume gsumval.o: |- O = { s e. B | A. t e. B ( ( s .+ t ) = t /\ ( t .+ s ) = t ) }
  assume gsumval.w: |- ( ph -> W = ( `' F " ( _V \ O ) ) )
  assume gsumval.g: |- ( ph -> G e. V )
  assume gsumval.a: |- ( ph -> A e. X )
  assume gsumval.f: |- ( ph -> F : A --> B )

  disjoint s t
  disjoint s x
  disjoint B s
  disjoint t x
  disjoint B t
  disjoint B x
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f ph
  disjoint m n
  disjoint m x
  disjoint m ph
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint F f
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint .+ s
  disjoint .+ t
  disjoint .+ x
  disjoint O f
  disjoint O m
  disjoint O n
  disjoint O x
  disjoint g o
  disjoint g w
  disjoint .0. g
  disjoint o w
  disjoint .0. o
  disjoint .0. w
  disjoint s y
  disjoint t y
  disjoint x y
  disjoint B y
  disjoint f g
  disjoint f o
  disjoint f w
  disjoint f y
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g ph
  disjoint m o
  disjoint m w
  disjoint m y
  disjoint n o
  disjoint n w
  disjoint n y
  disjoint o x
  disjoint o y
  disjoint o ph
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint ph y
  disjoint F g
  disjoint F o
  disjoint F w
  disjoint F y
  disjoint G g
  disjoint G o
  disjoint G w
  disjoint G y
  disjoint W g
  disjoint W o
  disjoint W w
  disjoint W y
  disjoint g s
  disjoint g t
  disjoint .+ g
  disjoint o s
  disjoint o t
  disjoint .+ o
  disjoint s w
  disjoint t w
  disjoint .+ w
  disjoint .+ y
  disjoint A g
  disjoint A o
  disjoint A w
  disjoint O g
  disjoint O o
  disjoint O w
  disjoint O y
  assert |- ( ph -> ( G gsum F ) = if ( ran F C_ O , .0. , if ( A e. ran ... , ( iota x E. m E. n e. ( ZZ>= ` m ) ( A = ( m ... n ) /\ x = ( seq m ( .+ , F ) ` n ) ) ) , ( iota x E. f ( f : ( 1 ... ( # ` W ) ) -1-1-onto-> W /\ x = ( seq 1 ( .+ , ( F o. f ) ) ` ( # ` W ) ) ) ) ) ) )

  proof
    wph
    vx
    vt
    cA
    cB
    c.pl
    vf
    vm
    vn
    cF
    cG
    cO
    cV
    cW
    cvv
    c.0
    vs
    gsumval.b
    gsumval.z
    gsumval.p
    gsumval.o
    gsumval.w
    gsumval.g
    wph
    cA
    cB
    cF
    wf
    #
    cA
    cX
    wcel
    cB
    cvv
    wcel
    #
    cF
    cvv
    wcel
    gsumval.f
    gsumval.a
    @1
    wph
    cB
    cG
    cbs
    cfv
    cvv
    gsumval.b
    cG
    cbs
    fvex
    eqeltri
    a1i
    cA
    cB
    cF
    cX
    cvv
    fex2
    syl3anc
    wph
    @0
    cF
    cdm
    cA
    wceq
    gsumval.f
    cA
    cB
    cF
    fdm
    syl
    gsumvalx
end
