include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "cotp.mm"
include "csplice.mm"
include "cconcat.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "splval.mm"
include "mp3anr3.mm"
include "simpl.mm"
include "cuz.mm"
include "elfzuz.mm"
include "ad2antrl.mm"
include "eluzfz1.mm"
include "syl.mm"
include "simprl.mm"
include "simprr.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "ad2antll.mm"
include "elfzuz2.mm"
include "eluzfz2.mm"
include "swrdid.mm"
include "adantr.mm"
include "eqtrd.mm"

theorem splid
  let cA: class A
  let cS: class S
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vs: setvar s
  let cF: class F
  let cR: class R
  let cT: class T
  let cV: class V
  let cW: class W


  assert |- ( ( S e. Word A /\ ( X e. ( 0 ... Y ) /\ Y e. ( 0 ... ( # ` S ) ) ) ) -> ( S splice <. X , Y , ( S substr <. X , Y >. ) >. ) = S )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cX
    cc0
    cY
    cfz
    co
    #
    wcel
    #
    cY
    cc0
    cS
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    cS
    cX
    cY
    cS
    cX
    cY
    cop
    #
    csubstr
    co
    #
    cotp
    csplice
    co
    #
    cS
    cc0
    cX
    cop
    csubstr
    co
    @10
    cconcat
    co
    #
    cS
    cY
    @4
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cS
    @1
    @3
    @6
    @10
    cvv
    wcel
    @11
    @14
    wceq
    cS
    @9
    csubstr
    ovex
    @10
    cS
    cY
    cX
    @0
    @2
    @5
    cvv
    splval
    mp3anr3
    @8
    @14
    cS
    cc0
    cY
    cop
    csubstr
    co
    #
    @13
    cconcat
    co
    #
    cS
    @8
    @12
    @15
    @13
    cconcat
    @8
    @1
    cc0
    cc0
    cX
    cfz
    co
    wcel
    #
    @3
    @6
    @12
    @15
    wceq
    @1
    @7
    simpl
    #
    @8
    cX
    cc0
    cuz
    cfv
    #
    wcel
    #
    @17
    @3
    @20
    @1
    @6
    cX
    cc0
    cY
    elfzuz
    ad2antrl
    cc0
    cX
    eluzfz1
    syl
    @1
    @3
    @6
    simprl
    @1
    @3
    @6
    simprr
    #
    cA
    cS
    cc0
    cX
    cY
    ccatswrd
    syl13anc
    oveq1d
    @8
    @16
    cS
    cc0
    @4
    cop
    csubstr
    co
    #
    cS
    @8
    @1
    cc0
    @2
    wcel
    #
    @6
    @4
    @5
    wcel
    #
    @16
    @22
    wceq
    @18
    @8
    cY
    @19
    wcel
    #
    @23
    @6
    @25
    @1
    @3
    cY
    cc0
    @4
    elfzuz
    ad2antll
    cc0
    cY
    eluzfz1
    syl
    @21
    @8
    @4
    @19
    wcel
    #
    @24
    @6
    @26
    @1
    @3
    cY
    cc0
    @4
    elfzuz2
    ad2antll
    cc0
    @4
    eluzfz2
    syl
    cA
    cS
    cc0
    cY
    @4
    ccatswrd
    syl13anc
    @1
    @22
    cS
    wceq
    @7
    cA
    cS
    swrdid
    adantr
    eqtrd
    eqtrd
    eqtrd
end
