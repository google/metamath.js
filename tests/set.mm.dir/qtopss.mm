include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "cqtop.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "toponss.mm"
include "3ad2antl2.mm"
include "cnima.mm"
include "3ad2antl1.mm"
include "cuni.mm"
include "wfo.mm"
include "wb.mm"
include "ctop.mm"
include "simpl1.mm"
include "cntop1.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wfn.mm"
include "wf.mm"
include "simpl2.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffn.mm"
include "simpl3.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "elqtop3.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"

theorem qtopss
  let cF: class F
  let cJ: class J
  let cK: class K
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cZ: class Z
  let cG: class G
  let wph: wff ph


  assert |- ( ( F e. ( J Cn K ) /\ K e. ( TopOn ` Y ) /\ ran F = Y ) -> K C_ ( J qTop F ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cF
    crn
    cY
    wceq
    #
    w3a
    #
    vx
    cK
    cJ
    cF
    cqtop
    co
    #
    @3
    vx
    cv
    #
    cK
    wcel
    #
    @5
    @4
    wcel
    #
    @3
    @6
    wa
    #
    @7
    @5
    cY
    wss
    #
    cF
    ccnv
    @5
    cima
    cJ
    wcel
    #
    @1
    @0
    @6
    @9
    @2
    @5
    cK
    cY
    toponss
    3ad2antl2
    @0
    @1
    @6
    @10
    @2
    @5
    cF
    cJ
    cK
    cnima
    3ad2antl1
    @8
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @11
    cY
    cF
    wfo
    #
    @7
    @9
    @10
    wa
    wb
    @8
    cJ
    ctop
    wcel
    #
    @12
    @8
    @0
    @14
    @0
    @1
    @2
    @6
    simpl1
    #
    cF
    cJ
    cK
    cntop1
    syl
    cJ
    @11
    @11
    eqid
    toptopon
    sylib
    #
    @8
    cF
    @11
    wfn
    #
    @2
    @13
    @8
    @11
    cY
    cF
    wf
    #
    @17
    @8
    @12
    @1
    @0
    @18
    @16
    @0
    @1
    @2
    @6
    simpl2
    @15
    cF
    cJ
    cK
    @11
    cY
    cnf2
    syl3anc
    @11
    cY
    cF
    ffn
    syl
    @0
    @1
    @2
    @6
    simpl3
    @11
    cY
    cF
    df-fo
    sylanbrc
    @5
    cF
    cJ
    @11
    cY
    elqtop3
    syl2anc
    mpbir2and
    ex
    ssrdv
end
