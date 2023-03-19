include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cioo.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "cexp.mm"
include "cc.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "wa.mm"
include "iccssre.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sselda.mm"
include "3adantl3.mm"
include "sincld.mm"
include "simpl3.mm"
include "expcld.mm"
include "ibliccsinexp.mm"
include "iblss.mm"

theorem iblioosinexp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint N x
  disjoint k x
  assert |- ( ( A e. RR /\ B e. RR /\ N e. NN0 ) -> ( x e. ( A (,) B ) |-> ( ( sin ` x ) ^ N ) ) e. L^1 )

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
    w3a
    #
    vx
    cA
    cB
    cioo
    co
    #
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
    cc
    @4
    @5
    wss
    @3
    cA
    cB
    ioossicc
    a1i
    @4
    cvol
    cdm
    wcel
    @3
    cA
    cB
    ioombl
    a1i
    @3
    @6
    @5
    wcel
    #
    wa
    #
    @7
    cN
    @9
    @6
    @0
    @1
    @8
    @6
    cc
    wcel
    @2
    @0
    @1
    wa
    #
    @5
    cc
    @6
    @10
    @5
    cr
    cc
    cA
    cB
    iccssre
    ax-resscn
    syl6ss
    sselda
    3adantl3
    sincld
    @0
    @1
    @2
    @8
    simpl3
    expcld
    vx
    cA
    cB
    cN
    ibliccsinexp
    iblss
end
