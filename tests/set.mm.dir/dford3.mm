include "word.mm"
include "wtr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "ordtr.mm"
include "wcel.mm"
include "ordelord.mm"
include "syl.mm"
include "ralrimiva.mm"
include "jca.mm"
include "con0.mm"
include "wss.mm"
include "simpl.mm"
include "dford3lem1.mm"
include "dford3lem2.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "ordon.mm"
include "a1i.mm"
include "trssord.mm"
include "syl3anc.mm"
include "impbii.mm"

theorem dford3
  let vx: setvar x
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y

  disjoint N x
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N y
  assert |- ( Ord N <-> ( Tr N /\ A. x e. N Tr x ) )

  proof
    cN
    word
    #
    cN
    wtr
    #
    vx
    cv
    #
    wtr
    #
    vx
    cN
    wral
    #
    wa
    #
    @0
    @1
    @4
    cN
    ordtr
    @0
    @3
    vx
    cN
    @0
    @2
    cN
    wcel
    wa
    @2
    word
    @3
    cN
    @2
    ordelord
    @2
    ordtr
    syl
    ralrimiva
    jca
    @5
    @1
    cN
    con0
    wss
    #
    con0
    word
    #
    @0
    @1
    @4
    simpl
    @5
    va
    cv
    #
    con0
    wcel
    #
    va
    cN
    wral
    #
    @6
    @5
    @8
    wtr
    @3
    vx
    @8
    wral
    wa
    #
    va
    cN
    wral
    @10
    vx
    cN
    va
    dford3lem1
    @11
    @9
    va
    cN
    va
    vx
    dford3lem2
    ralimi
    syl
    va
    cN
    con0
    dfss3
    sylibr
    @7
    @5
    ordon
    a1i
    cN
    con0
    trssord
    syl3anc
    impbii
end
