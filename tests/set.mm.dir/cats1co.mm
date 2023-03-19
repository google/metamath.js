include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "wceq.mm"
include "s1cld.mm"
include "ccatco.mm"
include "syl3anc.mm"
include "s1co.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "coeq2i.mm"
include "3eqtr4g.mm"

theorem cats1co
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cld.2: |- ( ph -> S e. Word A )
  assume cats1cld.3: |- ( ph -> X e. A )
  assume cats1co.4: |- ( ph -> F : A --> B )
  assume cats1co.5: |- ( ph -> ( F o. S ) = U )
  assume cats1co.6: |- V = ( U ++ <" ( F ` X ) "> )


  assert |- ( ph -> ( F o. T ) = V )

  proof
    wph
    cF
    cS
    cX
    cs1
    #
    cconcat
    co
    #
    ccom
    #
    cU
    cX
    cF
    cfv
    cs1
    #
    cconcat
    co
    #
    cF
    cT
    ccom
    cV
    wph
    @2
    cF
    cS
    ccom
    #
    cF
    @0
    ccom
    #
    cconcat
    co
    #
    @4
    wph
    cS
    cA
    cword
    #
    wcel
    @0
    @8
    wcel
    cA
    cB
    cF
    wf
    #
    @2
    @7
    wceq
    cats1cld.2
    wph
    cX
    cA
    cats1cld.3
    s1cld
    cats1co.4
    cA
    cB
    cS
    @0
    cF
    ccatco
    syl3anc
    wph
    @5
    cU
    @6
    @3
    cconcat
    cats1co.5
    wph
    cX
    cA
    wcel
    @9
    @6
    @3
    wceq
    cats1cld.3
    cats1co.4
    cA
    cB
    cX
    cF
    s1co
    syl2anc
    oveq12d
    eqtrd
    cT
    @1
    cF
    cats1cld.1
    coeq2i
    cats1co.6
    3eqtr4g
end
