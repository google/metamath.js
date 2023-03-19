include "cuspgr.mm"
include "wcel.mm"
include "cword.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "cclwwlk.mm"
include "clsw.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cclwlks.mm"
include "wex.mm"
include "lswccats1fst.mm"
include "3adant1.mm"
include "biantrurd.mm"
include "wrdlenccats1lenm1.mm"
include "adantr.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "simpl.mm"
include "wrdsymb1.mm"
include "s1cld.mm"
include "eqidd.mm"
include "swrdccatid.mm"
include "syl3anc.mm"
include "eqtr2d.mm"
include "eleq1d.mm"
include "c2.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "caddc.mm"
include "cn0.mm"
include "lencl.mm"
include "1e2m1.mm"
include "a1i.mm"
include "breq1d.mm"
include "cr.mm"
include "2re.mm"
include "1red.mm"
include "nn0re.mm"
include "lesubaddd.mm"
include "bitrd.mm"
include "syl.mm"
include "biimpa.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6breqr.mm"
include "jca.mm"
include "ccatlen.mm"
include "breqtrrd.mm"
include "clwlkclwwlk.mm"
include "3bitr4rd.mm"

theorem clwlkclwwlk2
  let cP: class P
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vi: setvar i
  let vx: setvar x
  let cR: class R
  let cF: class F
  assume clwlkclwwlk.v: |- V = ( Vtx ` G )
  assume clwlkclwwlk.e: |- E = ( iEdg ` G )

  disjoint E f
  disjoint P f
  disjoint V f
  disjoint G f
  disjoint E i
  disjoint E x
  disjoint f i
  disjoint f x
  disjoint i x
  disjoint P i
  disjoint P x
  disjoint R f
  disjoint R i
  disjoint R x
  disjoint V i
  disjoint V x
  disjoint F i
  disjoint G i
  assert |- ( ( G e. USPGraph /\ P e. Word V /\ 1 <_ ( # ` P ) ) -> ( E. f f ( ClWalks ` G ) ( P ++ <" ( P ` 0 ) "> ) <-> P e. ( ClWWalks ` G ) ) )

  proof
    cG
    cuspgr
    wcel
    #
    cP
    cV
    cword
    #
    wcel
    #
    c1
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    cP
    cc0
    cP
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cc0
    @8
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    @8
    clsw
    cfv
    cc0
    @8
    cfv
    wceq
    #
    @14
    wa
    #
    cP
    @13
    wcel
    vf
    cv
    @8
    cG
    cclwlks
    cfv
    wbr
    vf
    wex
    #
    @5
    @15
    @14
    @2
    @4
    @15
    @0
    cP
    cV
    lswccats1fst
    3adant1
    biantrurd
    @5
    cP
    @12
    @13
    @2
    @4
    cP
    @12
    wceq
    @0
    @2
    @4
    wa
    #
    @12
    @8
    cc0
    @3
    cop
    #
    csubstr
    co
    #
    cP
    @18
    @11
    @19
    @8
    csubstr
    @18
    @10
    @3
    cc0
    @2
    @10
    @3
    wceq
    @4
    @6
    cV
    cP
    wrdlenccats1lenm1
    adantr
    opeq2d
    oveq2d
    @18
    @2
    @7
    @1
    wcel
    #
    @3
    @3
    wceq
    @20
    cP
    wceq
    @2
    @4
    simpl
    #
    @18
    @6
    cV
    cV
    cP
    wrdsymb1
    s1cld
    #
    @18
    @3
    eqidd
    cP
    @7
    @3
    cV
    swrdccatid
    syl3anc
    eqtr2d
    3adant1
    eleq1d
    @5
    @0
    @8
    @1
    wcel
    #
    c2
    @9
    cle
    wbr
    @17
    @16
    wb
    @0
    @2
    @4
    simp1
    @5
    @2
    @21
    @24
    @0
    @2
    @4
    simp2
    @2
    @4
    @21
    @0
    @23
    3adant1
    cV
    cP
    @7
    ccatcl
    syl2anc
    @5
    c2
    @3
    @7
    chash
    cfv
    #
    caddc
    co
    #
    @9
    cle
    @2
    @4
    c2
    @26
    cle
    wbr
    @0
    @18
    c2
    @3
    c1
    caddc
    co
    #
    @26
    cle
    @2
    @4
    c2
    @27
    cle
    wbr
    #
    @2
    @3
    cn0
    wcel
    #
    @4
    @28
    wb
    cV
    cP
    lencl
    @29
    @4
    c2
    c1
    cmin
    co
    #
    @3
    cle
    wbr
    @28
    @29
    c1
    @30
    @3
    cle
    c1
    @30
    wceq
    @29
    1e2m1
    a1i
    breq1d
    @29
    c2
    c1
    @3
    c2
    cr
    wcel
    @29
    2re
    a1i
    @29
    1red
    @3
    nn0re
    lesubaddd
    bitrd
    syl
    biimpa
    @25
    c1
    @3
    caddc
    @6
    s1len
    oveq2i
    syl6breqr
    3adant1
    @5
    @2
    @21
    wa
    #
    @9
    @26
    wceq
    @2
    @4
    @31
    @0
    @18
    @2
    @21
    @22
    @23
    jca
    3adant1
    cV
    cP
    @7
    ccatlen
    syl
    breqtrrd
    @8
    vf
    cE
    cG
    cV
    clwlkclwwlk.v
    clwlkclwwlk.e
    clwlkclwwlk
    syl3anc
    3bitr4rd
end
