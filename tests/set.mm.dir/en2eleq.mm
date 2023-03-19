include "wcel.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cpr.mm"
include "cfn.mm"
include "wss.mm"
include "wceq.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "enfi.mm"
include "mpbiri.mm"
include "adantl.mm"
include "simpl.mm"
include "wne.mm"
include "c1o.mm"
include "csuc.mm"
include "1onn.mm"
include "a1i.mm"
include "simpr.mm"
include "df-2o.mm"
include "syl6breq.mm"
include "dif1en.mm"
include "syl3anc.mm"
include "en1uniel.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "prssi.mm"
include "syl2anc.mm"
include "simprd.mm"
include "necomd.mm"
include "pr2nelem.mm"
include "ensym.mm"
include "entr.mm"
include "fisseneq.mm"
include "eqcomd.mm"

theorem en2eleq
  let cP: class P
  let cX: class X


  assert |- ( ( X e. P /\ P ~~ 2o ) -> P = { X , U. ( P \ { X } ) } )

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
    cX
    cP
    cX
    csn
    cdif
    #
    cuni
    #
    cpr
    #
    cP
    @2
    cP
    cfn
    wcel
    #
    @5
    cP
    wss
    #
    @5
    cP
    cen
    wbr
    #
    @5
    cP
    wceq
    @1
    @6
    @0
    @1
    @6
    c2o
    cfn
    wcel
    #
    c2o
    com
    wcel
    @9
    2onn
    c2o
    nnfi
    ax-mp
    cP
    c2o
    enfi
    mpbiri
    adantl
    @2
    @0
    @4
    cP
    wcel
    #
    @7
    @0
    @1
    simpl
    #
    @2
    @10
    @4
    cX
    wne
    #
    @2
    @4
    @3
    wcel
    #
    @10
    @12
    wa
    @2
    @3
    c1o
    cen
    wbr
    #
    @13
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
    @14
    @15
    @2
    1onn
    a1i
    @2
    cP
    c2o
    @16
    cen
    @0
    @1
    simpr
    df-2o
    syl6breq
    @11
    cP
    c1o
    cX
    dif1en
    syl3anc
    @3
    en1uniel
    syl
    @4
    cP
    cX
    eldifsn
    sylib
    #
    simpld
    #
    cX
    @4
    cP
    prssi
    syl2anc
    @2
    @5
    c2o
    cen
    wbr
    #
    c2o
    cP
    cen
    wbr
    #
    @8
    @2
    @0
    @10
    cX
    @4
    wne
    @19
    @11
    @18
    @2
    @4
    cX
    @2
    @10
    @12
    @17
    simprd
    necomd
    cX
    @4
    cP
    cP
    pr2nelem
    syl3anc
    @1
    @20
    @0
    cP
    c2o
    ensym
    adantl
    @5
    c2o
    cP
    entr
    syl2anc
    @5
    cP
    fisseneq
    syl3anc
    eqcomd
end
