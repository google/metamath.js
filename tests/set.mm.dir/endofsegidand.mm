include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wceq.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "endofsegid.mm"
include "syl13anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem endofsegidand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  assume endofsegidand.1: |- ( ph -> N e. NN )
  assume endofsegidand.2: |- ( ph -> A e. ( EE ` N ) )
  assume endofsegidand.3: |- ( ph -> B e. ( EE ` N ) )
  assume endofsegidand.4: |- ( ph -> C e. ( EE ` N ) )
  assume endofsegidand.5: |- ( ( ph /\ ps ) -> C Btwn <. A , B >. )
  assume endofsegidand.6: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. A , C >. )


  assert |- ( ( ph /\ ps ) -> B = C )

  proof
    wph
    wps
    wa
    cC
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    @0
    cA
    cC
    cop
    ccgr
    wbr
    #
    cB
    cC
    wceq
    #
    endofsegidand.5
    endofsegidand.6
    wph
    @1
    @2
    wa
    @3
    wi
    #
    wps
    wph
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cC
    @5
    wcel
    cB
    @5
    wcel
    @4
    endofsegidand.1
    endofsegidand.2
    endofsegidand.4
    endofsegidand.3
    cA
    cC
    cB
    cN
    endofsegid
    syl13anc
    adantr
    mp2and
end
