include "clt.mm"
include "cv.mm"
include "cfv.mm"
include "ltle.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "idd.mm"
include "nmoleub2lem2.mm"

theorem nmoleub2b
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let wps: wff ps
  let cB: class B
  assume nmoleub2.n: |- N = ( S normOp T )
  assume nmoleub2.v: |- V = ( Base ` S )
  assume nmoleub2.l: |- L = ( norm ` S )
  assume nmoleub2.m: |- M = ( norm ` T )
  assume nmoleub2.g: |- G = ( Scalar ` S )
  assume nmoleub2.w: |- K = ( Base ` G )
  assume nmoleub2.s: |- ( ph -> S e. ( NrmMod i^i CMod ) )
  assume nmoleub2.t: |- ( ph -> T e. ( NrmMod i^i CMod ) )
  assume nmoleub2.f: |- ( ph -> F e. ( S LMHom T ) )
  assume nmoleub2.a: |- ( ph -> A e. RR* )
  assume nmoleub2.r: |- ( ph -> R e. RR+ )
  assume nmoleub2a.5: |- ( ph -> QQ C_ K )

  disjoint A x
  disjoint F x
  disjoint L x
  disjoint N x
  disjoint M x
  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint R x
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F r
  disjoint F y
  disjoint F z
  disjoint L r
  disjoint L y
  disjoint L z
  disjoint N y
  disjoint O y
  disjoint O z
  disjoint M r
  disjoint M y
  disjoint M z
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint S y
  disjoint S z
  disjoint V y
  disjoint V z
  disjoint B r
  disjoint R r
  disjoint R y
  disjoint R z
  disjoint T y
  assert |- ( ph -> ( ( N ` F ) <_ A <-> A. x e. V ( ( L ` x ) < R -> ( ( M ` ( F ` x ) ) / R ) <_ A ) ) )

  proof
    wph
    vx
    cA
    cR
    cS
    cT
    cF
    cG
    cK
    cL
    cM
    cN
    clt
    cV
    nmoleub2.n
    nmoleub2.v
    nmoleub2.l
    nmoleub2.m
    nmoleub2.g
    nmoleub2.w
    nmoleub2.s
    nmoleub2.t
    nmoleub2.f
    nmoleub2.a
    nmoleub2.r
    nmoleub2a.5
    vx
    cv
    cL
    cfv
    #
    cR
    ltle
    @0
    cr
    wcel
    cR
    cr
    wcel
    wa
    @0
    cR
    clt
    wbr
    idd
    nmoleub2lem2
end
