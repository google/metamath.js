include "wcel.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cpr.mm"
include "en2eleq.mm"
include "prcom.mm"
include "syl6eq.mm"
include "difeq1d.mm"
include "difprsnss.mm"
include "syl6eqss.mm"
include "wne.mm"
include "simpl.mm"
include "c1o.mm"
include "com.mm"
include "csuc.mm"
include "1onn.mm"
include "a1i.mm"
include "simpr.mm"
include "df-2o.mm"
include "syl6breq.mm"
include "dif1en.mm"
include "syl3anc.mm"
include "en1uniel.mm"
include "eldifsni.mm"
include "3syl.mm"
include "necomd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "eqssd.mm"
include "unieqd.mm"
include "wceq.mm"
include "unisng.mm"
include "adantr.mm"
include "eqtrd.mm"

theorem en2other2
  let cP: class P
  let cX: class X


  assert |- ( ( X e. P /\ P ~~ 2o ) -> U. ( P \ { U. ( P \ { X } ) } ) = X )

  proof
    cX
    cP
    wcel
    #
    cP
    c2o
    cen
    wbr
    #
    wa
    #
    cP
    cP
    cX
    csn
    #
    cdif
    #
    cuni
    #
    csn
    #
    cdif
    #
    cuni
    @3
    cuni
    #
    cX
    @2
    @7
    @3
    @2
    @7
    @3
    @2
    @7
    @5
    cX
    cpr
    #
    @6
    cdif
    @3
    @2
    cP
    @9
    @6
    @2
    cP
    cX
    @5
    cpr
    @9
    cP
    cX
    en2eleq
    cX
    @5
    prcom
    syl6eq
    difeq1d
    @5
    cX
    difprsnss
    syl6eqss
    @2
    cX
    @7
    @2
    @0
    cX
    @5
    wne
    cX
    @7
    wcel
    @0
    @1
    simpl
    #
    @2
    @5
    cX
    @2
    @4
    c1o
    cen
    wbr
    #
    @5
    @4
    wcel
    @5
    cX
    wne
    @2
    c1o
    com
    wcel
    #
    cP
    c1o
    csuc
    #
    cen
    wbr
    @0
    @11
    @12
    @2
    1onn
    a1i
    @2
    cP
    c2o
    @13
    cen
    @0
    @1
    simpr
    df-2o
    syl6breq
    @10
    cP
    c1o
    cX
    dif1en
    syl3anc
    @4
    en1uniel
    @5
    cP
    cX
    eldifsni
    3syl
    necomd
    cX
    cP
    @5
    eldifsn
    sylanbrc
    snssd
    eqssd
    unieqd
    @0
    @8
    cX
    wceq
    @1
    cX
    cP
    unisng
    adantr
    eqtrd
end
