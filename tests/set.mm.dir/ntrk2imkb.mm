include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "id.mm"
include "weq.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "raaanv.mm"
include "sylanbrc.mm"
include "ss2in.mm"
include "adantr.mm"
include "simpr.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "syl.mm"
include "ex.mm"
include "2ralimi.mm"

theorem ntrk2imkb
  let vt: setvar t
  let cB: class B
  let cI: class I
  let vs: setvar s

  disjoint B s
  disjoint B t
  disjoint s t
  disjoint I s
  disjoint I t
  assert |- ( A. s e. ~P B ( I ` s ) C_ s -> A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/) -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) )

  proof
    vs
    cv
    #
    cI
    cfv
    #
    @0
    wss
    #
    vs
    cB
    cpw
    #
    wral
    #
    @2
    vt
    cv
    #
    cI
    cfv
    #
    @5
    wss
    #
    wa
    #
    vt
    @3
    wral
    vs
    @3
    wral
    #
    @0
    @5
    cin
    #
    c0
    wceq
    #
    @1
    @6
    cin
    #
    c0
    wceq
    #
    wi
    #
    vt
    @3
    wral
    vs
    @3
    wral
    @4
    @4
    @7
    vt
    @3
    wral
    #
    @9
    @4
    id
    @4
    @15
    @2
    @7
    vs
    vt
    @3
    vs
    vt
    weq
    #
    @1
    @6
    @0
    @5
    @0
    @5
    cI
    fveq2
    @16
    id
    sseq12d
    cbvralv
    biimpi
    @2
    @7
    vs
    vt
    @3
    raaanv
    sylanbrc
    @8
    @14
    vs
    vt
    @3
    @3
    @8
    @11
    @13
    @8
    @11
    wa
    #
    @12
    c0
    wss
    @13
    @17
    @12
    @10
    c0
    @8
    @12
    @10
    wss
    @11
    @1
    @0
    @6
    @5
    ss2in
    adantr
    @8
    @11
    simpr
    sseqtrd
    @12
    ss0
    syl
    ex
    2ralimi
    syl
end
