include "cquot.mm"
include "co.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cmul.mm"
include "cof.mm"
include "cmin.mm"
include "c0p.mm"
include "wceq.mm"
include "cdgr.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "eqid.mm"
include "quotlem.mm"
include "simpld.mm"

theorem quotcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cG: class G
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let vp: setvar p
  let vq: setvar q
  let cH: class H
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  let cT: class T
  let vg: setvar g
  let vw: setvar w
  let cR: class R
  assume plydiv.pl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plydiv.tm: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plydiv.rc: |- ( ( ph /\ ( x e. S /\ x =/= 0 ) ) -> ( 1 / x ) e. S )
  assume plydiv.m1: |- ( ph -> -u 1 e. S )
  assume plydiv.f: |- ( ph -> F e. ( Poly ` S ) )
  assume plydiv.g: |- ( ph -> G e. ( Poly ` S ) )
  assume plydiv.z: |- ( ph -> G =/= 0p )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint d ph
  disjoint ph z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N f
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint T x
  disjoint T y
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint G f
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint G p
  disjoint q w
  disjoint G q
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R p
  disjoint R x
  disjoint R y
  disjoint S d
  disjoint S f
  disjoint S g
  disjoint S p
  disjoint S q
  disjoint S z
  assert |- ( ph -> ( F quot G ) e. ( Poly ` S ) )

  proof
    wph
    cF
    cG
    cquot
    co
    #
    cS
    cply
    cfv
    wcel
    cF
    cG
    @0
    cmul
    cof
    co
    cmin
    cof
    co
    #
    c0p
    wceq
    @1
    cdgr
    cfv
    cG
    cdgr
    cfv
    clt
    wbr
    wo
    wph
    vx
    vy
    @1
    cS
    cF
    cG
    plydiv.pl
    plydiv.tm
    plydiv.rc
    plydiv.m1
    plydiv.f
    plydiv.g
    plydiv.z
    @1
    eqid
    quotlem
    simpld
end
