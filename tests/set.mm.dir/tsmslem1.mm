include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "adantr.mm"
include "simpr.mm"
include "wf.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "syl6eleq.mm"
include "elfpw.mm"
include "simplbi.mm"
include "syl.mm"
include "fssresd.mm"
include "cvv.mm"
include "simprbi.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"

theorem tsmslem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cW: class W
  let cX: class X
  assume tsmslem1.b: |- B = ( Base ` G )
  assume tsmslem1.s: |- S = ( ~P A i^i Fin )
  assume tsmslem1.1: |- ( ph -> G e. CMnd )
  assume tsmslem1.a: |- ( ph -> A e. W )
  assume tsmslem1.f: |- ( ph -> F : A --> B )


  assert |- ( ( ph /\ X e. S ) -> ( G gsum ( F |` X ) ) e. B )

  proof
    wph
    cX
    cS
    wcel
    #
    wa
    #
    cX
    cB
    cF
    cX
    cres
    #
    cG
    cS
    cG
    c0g
    cfv
    #
    tsmslem1.b
    @3
    eqid
    wph
    cG
    ccmn
    wcel
    @0
    tsmslem1.1
    adantr
    wph
    @0
    simpr
    #
    @1
    cA
    cB
    cX
    cF
    wph
    cA
    cB
    cF
    wf
    @0
    tsmslem1.f
    adantr
    @1
    cX
    cA
    cpw
    cfn
    cin
    #
    wcel
    #
    cX
    cA
    wss
    #
    @1
    cX
    cS
    @5
    @4
    tsmslem1.s
    syl6eleq
    #
    @6
    @7
    cX
    cfn
    wcel
    #
    cX
    cA
    elfpw
    #
    simplbi
    syl
    fssresd
    #
    @1
    cX
    cB
    @2
    cvv
    @3
    @11
    @1
    @6
    @9
    @8
    @6
    @7
    @9
    @10
    simprbi
    syl
    @1
    cG
    c0g
    fvexd
    fdmfifsupp
    gsumcl
end
