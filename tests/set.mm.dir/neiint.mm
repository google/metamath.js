include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cnei.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cnt.mm"
include "wb.mm"
include "isnei.mm"
include "3adant3.mm"
include "3anibar.mm"
include "simprrl.mm"
include "ssntr.mm"
include "3adantl2.mm"
include "adantrrl.mm"
include "sstrd.mm"
include "rexlimdvaa.mm"
include "simpl1.mm"
include "simpl3.mm"
include "ntropn.mm"
include "syl2anc.mm"
include "simpr.mm"
include "ntrss2.mm"
include "wceq.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"

theorem neiint
  let cS: class S
  let cJ: class J
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  assume neifval.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X /\ N C_ X ) -> ( N e. ( ( nei ` J ) ` S ) <-> S C_ ( ( int ` J ) ` N ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cN
    cX
    wss
    #
    w3a
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cS
    vv
    cv
    #
    wss
    #
    @5
    cN
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    cS
    cN
    cJ
    cnt
    cfv
    cfv
    #
    wss
    #
    @0
    @1
    @2
    @4
    @9
    @0
    @1
    @4
    @2
    @9
    wa
    wb
    @2
    cS
    vv
    cJ
    cN
    cX
    neifval.1
    isnei
    3adant3
    3anibar
    @3
    @9
    @11
    @3
    @8
    @11
    vv
    cJ
    @3
    @5
    cJ
    wcel
    #
    @8
    wa
    wa
    cS
    @5
    @10
    @3
    @12
    @6
    @7
    simprrl
    @3
    @12
    @7
    @5
    @10
    wss
    #
    @6
    @0
    @2
    @12
    @7
    wa
    @13
    @1
    cN
    cJ
    @5
    cX
    neifval.1
    ssntr
    3adantl2
    adantrrl
    sstrd
    rexlimdvaa
    @3
    @11
    @9
    @3
    @11
    wa
    #
    @10
    cJ
    wcel
    #
    @11
    @10
    cN
    wss
    #
    @9
    @14
    @0
    @2
    @15
    @0
    @1
    @2
    @11
    simpl1
    #
    @0
    @1
    @2
    @11
    simpl3
    #
    cN
    cJ
    cX
    neifval.1
    ntropn
    syl2anc
    @3
    @11
    simpr
    @14
    @0
    @2
    @16
    @17
    @18
    cN
    cJ
    cX
    neifval.1
    ntrss2
    syl2anc
    @8
    @11
    @16
    wa
    vv
    @10
    cJ
    @5
    @10
    wceq
    @6
    @11
    @7
    @16
    @5
    @10
    cS
    sseq2
    @5
    @10
    cN
    sseq1
    anbi12d
    rspcev
    syl12anc
    ex
    impbid
    bitrd
end
