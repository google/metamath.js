include "cr.mm"
include "wss.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "cres.mm"
include "cdv.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "simpr.mm"
include "simpl.mm"
include "ioossre.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "ioontr.mm"
include "reseq2i.mm"
include "syl6eq.mm"

theorem dvresioo
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A C_ RR /\ F : A --> CC ) -> ( RR _D ( F |` ( B (,) C ) ) ) = ( ( RR _D F ) |` ( B (,) C ) ) )

  proof
    cA
    cr
    wss
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    cr
    cF
    cB
    cC
    cioo
    co
    #
    cres
    cdv
    co
    #
    cr
    cF
    cdv
    co
    #
    @3
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @5
    @3
    cres
    @2
    cr
    cc
    wss
    #
    @1
    @0
    @3
    cr
    wss
    #
    @4
    @8
    wceq
    @9
    @2
    ax-resscn
    a1i
    @0
    @1
    simpr
    @0
    @1
    simpl
    @10
    @2
    cB
    cC
    ioossre
    a1i
    cA
    @3
    cr
    @6
    cF
    ccnfld
    ctopn
    cfv
    #
    @11
    eqid
    #
    @11
    @12
    tgioo2
    dvres
    syl22anc
    @7
    @3
    @5
    cB
    cC
    ioontr
    reseq2i
    syl6eq
end
