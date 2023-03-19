include "com.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cop.mm"
include "cvv.mm"
include "wf1o.mm"
include "snex.mm"
include "f1osn.mm"
include "f1oen3g.mm"
include "mp2an.mm"
include "difss.mm"
include "ssexi.mm"
include "enref.mm"
include "pm3.2i.mm"
include "incom.mm"
include "wss.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "word.mm"
include "nnord.mm"
include "orddisj.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ss0.mm"
include "syl5eq.mm"
include "disjdif.mm"
include "jctil.mm"
include "unen.mm"
include "sylancr.mm"
include "adantr.mm"
include "uncom.mm"
include "difsnid.mm"
include "adantl.mm"
include "phplem1.mm"
include "3brtr3d.mm"

theorem phplem2
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume phplem2.1: |- A e. _V
  assume phplem2.2: |- B e. _V


  assert |- ( ( A e. _om /\ B e. A ) -> A ~~ ( suc A \ { B } ) )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    cB
    csn
    #
    cA
    @2
    cdif
    #
    cun
    #
    cA
    csn
    #
    @3
    cun
    #
    cA
    cA
    csuc
    @2
    cdif
    cen
    @0
    @4
    @6
    cen
    wbr
    #
    @1
    @0
    @2
    @5
    cen
    wbr
    #
    @3
    @3
    cen
    wbr
    #
    wa
    @2
    @3
    cin
    c0
    wceq
    #
    @5
    @3
    cin
    #
    c0
    wceq
    #
    wa
    @7
    @8
    @9
    cB
    cA
    cop
    #
    csn
    #
    cvv
    wcel
    @2
    @5
    @14
    wf1o
    @8
    @13
    snex
    cB
    cA
    phplem2.2
    phplem2.1
    f1osn
    @2
    @5
    @14
    cvv
    f1oen3g
    mp2an
    @3
    @3
    cA
    phplem2.1
    cA
    @2
    difss
    #
    ssexi
    enref
    pm3.2i
    @0
    @12
    @10
    @0
    @11
    @3
    @5
    cin
    #
    c0
    @5
    @3
    incom
    @0
    @16
    c0
    wss
    @16
    c0
    wceq
    @0
    cA
    @5
    cin
    #
    @16
    c0
    @3
    cA
    wss
    @16
    @17
    wss
    @15
    @3
    cA
    @5
    ssrin
    ax-mp
    @0
    cA
    word
    @17
    c0
    wceq
    cA
    nnord
    cA
    orddisj
    syl
    syl5sseq
    @16
    ss0
    syl
    syl5eq
    @2
    cA
    disjdif
    jctil
    @2
    @5
    @3
    @3
    unen
    sylancr
    adantr
    @1
    @4
    cA
    wceq
    @0
    @1
    @4
    @3
    @2
    cun
    cA
    @2
    @3
    uncom
    cA
    cB
    difsnid
    syl5eq
    adantl
    cA
    cB
    phplem1
    3brtr3d
end
