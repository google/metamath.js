include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "clmim.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "wfo.mm"
include "fofn.mm"
include "syl.mm"
include "cdm.mm"
include "clindf.mm"
include "wbr.mm"
include "clmod.mm"
include "lindff.mm"
include "syl2anc.mm"
include "frn.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "frlmup1.mm"
include "wf1.mm"
include "wceq.mm"
include "islindf5.mm"
include "mpbid.mm"
include "cfv.mm"
include "frlmup3.mm"
include "forn.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "dff1o5.mm"
include "islmim.mm"

theorem indlcim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  assume indlcim.f: |- F = ( R freeLMod I )
  assume indlcim.b: |- B = ( Base ` F )
  assume indlcim.c: |- C = ( Base ` T )
  assume indlcim.v: |- .x. = ( .s ` T )
  assume indlcim.n: |- N = ( LSpan ` T )
  assume indlcim.e: |- E = ( x e. B |-> ( T gsum ( x oF .x. A ) ) )
  assume indlcim.t: |- ( ph -> T e. LMod )
  assume indlcim.i: |- ( ph -> I e. X )
  assume indlcim.r: |- ( ph -> R = ( Scalar ` T ) )
  assume indlcim.a: |- ( ph -> A : I -onto-> J )
  assume indlcim.l: |- ( ph -> A LIndF T )
  assume indlcim.s: |- ( ph -> ( N ` J ) = C )

  disjoint ph x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint I x
  disjoint N x
  disjoint R x
  disjoint T x
  disjoint .x. x
  disjoint X x
  assert |- ( ph -> E e. ( F LMIso T ) )

  proof
    wph
    cE
    cF
    cT
    clmhm
    co
    wcel
    cB
    cC
    cE
    wf1o
    #
    cE
    cF
    cT
    clmim
    co
    wcel
    wph
    vx
    cA
    cB
    cC
    cR
    cT
    c.x
    cE
    cF
    cI
    cX
    indlcim.f
    indlcim.b
    indlcim.c
    indlcim.v
    indlcim.e
    indlcim.t
    indlcim.i
    indlcim.r
    wph
    cA
    cI
    wfn
    #
    cA
    crn
    #
    cC
    wss
    #
    cI
    cC
    cA
    wf
    wph
    cI
    cJ
    cA
    wfo
    #
    @1
    indlcim.a
    cI
    cJ
    cA
    fofn
    syl
    wph
    cA
    cdm
    #
    cC
    cA
    wf
    #
    @3
    wph
    cA
    cT
    clindf
    wbr
    #
    cT
    clmod
    wcel
    @6
    indlcim.l
    indlcim.t
    cC
    cA
    cT
    clmod
    indlcim.c
    lindff
    syl2anc
    @5
    cC
    cA
    frn
    syl
    cI
    cC
    cA
    df-f
    sylanbrc
    #
    frlmup1
    wph
    cB
    cC
    cE
    wf1
    #
    cE
    crn
    #
    cC
    wceq
    @0
    wph
    @7
    @9
    indlcim.l
    wph
    vx
    cA
    cB
    cC
    cR
    cT
    c.x
    cE
    cF
    cI
    cX
    indlcim.f
    indlcim.b
    indlcim.c
    indlcim.v
    indlcim.e
    indlcim.t
    indlcim.i
    indlcim.r
    @8
    islindf5
    mpbid
    wph
    @10
    @2
    cN
    cfv
    cJ
    cN
    cfv
    cC
    wph
    vx
    cA
    cB
    cC
    cR
    cT
    c.x
    cE
    cF
    cI
    cN
    cX
    indlcim.f
    indlcim.b
    indlcim.c
    indlcim.v
    indlcim.e
    indlcim.t
    indlcim.i
    indlcim.r
    @8
    indlcim.n
    frlmup3
    wph
    @2
    cJ
    cN
    wph
    @4
    @2
    cJ
    wceq
    indlcim.a
    cI
    cJ
    cA
    forn
    syl
    fveq2d
    indlcim.s
    3eqtrd
    cB
    cC
    cE
    dff1o5
    sylanbrc
    cB
    cC
    cF
    cT
    cE
    indlcim.b
    indlcim.c
    islmim
    sylanbrc
end
