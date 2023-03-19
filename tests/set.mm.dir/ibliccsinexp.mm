include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "cexp.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "cibl.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "iccssre.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sselda.mm"
include "3adantl3.mm"
include "sincld.mm"
include "simpl3.mm"
include "expcld.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "nfmpt1.mm"
include "nfcv.mm"
include "sincn.mm"
include "a1i.mm"
include "simp3.mm"
include "expcnfg.mm"
include "wss.mm"
include "3adant3.mm"
include "cncfmptss.mm"
include "eqeltrd.mm"
include "cniccibl.mm"
include "syld3an3.mm"

theorem ibliccsinexp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint N x
  disjoint k x
  assert |- ( ( A e. RR /\ B e. RR /\ N e. NN0 ) -> ( x e. ( A [,] B ) |-> ( ( sin ` x ) ^ N ) ) e. L^1 )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    vx
    cA
    cB
    cicc
    co
    #
    vx
    cv
    #
    csin
    cfv
    #
    cN
    cexp
    co
    #
    cmpt
    #
    @3
    cc
    ccncf
    co
    #
    wcel
    @7
    cibl
    wcel
    @0
    @1
    @2
    w3a
    #
    @7
    vx
    @3
    @4
    vx
    cc
    @6
    cmpt
    #
    cfv
    #
    cmpt
    @8
    @9
    vx
    @3
    @6
    @11
    @9
    @4
    @3
    wcel
    #
    wa
    #
    @11
    @6
    @13
    @4
    cc
    wcel
    #
    @6
    cc
    wcel
    @11
    @6
    wceq
    @0
    @1
    @12
    @14
    @2
    @0
    @1
    wa
    #
    @3
    cc
    @4
    @15
    @3
    cr
    cc
    cA
    cB
    iccssre
    ax-resscn
    syl6ss
    #
    sselda
    3adantl3
    #
    @13
    @5
    cN
    @13
    @4
    @17
    sincld
    @0
    @1
    @2
    @12
    simpl3
    expcld
    vx
    cc
    @6
    cc
    @10
    @10
    eqid
    fvmpt2
    syl2anc
    eqcomd
    mpteq2dva
    @9
    vx
    cc
    cc
    @3
    @10
    vx
    cc
    @6
    nfmpt1
    @9
    vx
    cc
    csin
    cN
    vx
    csin
    nfcv
    csin
    cc
    cc
    ccncf
    co
    wcel
    @9
    sincn
    a1i
    @0
    @1
    @2
    simp3
    expcnfg
    @0
    @1
    @3
    cc
    wss
    @2
    @16
    3adant3
    cncfmptss
    eqeltrd
    cA
    cB
    @7
    cniccibl
    syld3an3
end
