include "cui.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "sq1.mm"
include "cn.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "cgz.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "crg.mm"
include "wceq.mm"
include "wb.mm"
include "gzsubrg.mm"
include "subrgring.mm"
include "eqid.mm"
include "csubg.mm"
include "c0g.mm"
include "subrgsubg.mm"
include "cnfld0.mm"
include "subg0.mm"
include "mp2b.mm"
include "cur.mm"
include "cnfld1.mm"
include "subrg1.mm"
include "ax-mp.mm"
include "0unit.mm"
include "nemtbir.mm"
include "wn.mm"
include "cn0.mm"
include "wo.mm"
include "cbs.mm"
include "subrgbas.mm"
include "unitcl.mm"
include "gzabssqcl.mm"
include "syl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "cc.mm"
include "gzcn.mm"
include "abscld.mm"
include "recnd.mm"
include "sqeq0.mm"
include "abs00ad.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "sylbid.mm"
include "syld.mm"
include "mt3i.mm"
include "nnge1d.mm"
include "syl5eqbr.mm"
include "cr.mm"
include "absge0d.mm"
include "wa.mm"
include "1re.mm"
include "0le1.mm"
include "le2sq.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem gzrngunitlem
  let cA: class A
  let cZ: class Z
  assume gzrng.1: |- Z = ( CCfld |`s Z[i] )


  assert |- ( A e. ( Unit ` Z ) -> 1 <_ ( abs ` A ) )

  proof
    cA
    cZ
    cui
    cfv
    #
    wcel
    #
    c1
    cA
    cabs
    cfv
    #
    cle
    wbr
    #
    c1
    c2
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @1
    @4
    c1
    @5
    cle
    sq1
    @1
    @5
    @1
    @5
    cn
    wcel
    #
    cc0
    @0
    wcel
    #
    @8
    c1
    cc0
    ax-1ne0
    cgz
    ccnfld
    csubrg
    cfv
    wcel
    #
    cZ
    crg
    wcel
    @8
    c1
    cc0
    wceq
    wb
    gzsubrg
    cgz
    ccnfld
    cZ
    gzrng.1
    subrgring
    cZ
    @0
    c1
    cc0
    @0
    eqid
    #
    @9
    cgz
    ccnfld
    csubg
    cfv
    wcel
    cc0
    cZ
    c0g
    cfv
    wceq
    gzsubrg
    cgz
    ccnfld
    subrgsubg
    cgz
    ccnfld
    cZ
    cc0
    gzrng.1
    cnfld0
    subg0
    mp2b
    @9
    c1
    cZ
    cur
    cfv
    wceq
    gzsubrg
    cgz
    ccnfld
    cZ
    c1
    gzrng.1
    cnfld1
    subrg1
    ax-mp
    0unit
    mp2b
    nemtbir
    @1
    @7
    wn
    @5
    cc0
    wceq
    #
    @8
    @1
    @7
    @11
    @1
    @5
    cn0
    wcel
    #
    @7
    @11
    wo
    @1
    cA
    cgz
    wcel
    #
    @12
    cgz
    cZ
    @0
    cA
    @9
    cgz
    cZ
    cbs
    cfv
    wceq
    gzsubrg
    cgz
    ccnfld
    cZ
    gzrng.1
    subrgbas
    ax-mp
    @10
    unitcl
    #
    cA
    gzabssqcl
    syl
    @5
    elnn0
    sylib
    ord
    @1
    @11
    @2
    cc0
    wceq
    #
    @8
    @1
    @2
    cc
    wcel
    @11
    @15
    wb
    @1
    @2
    @1
    cA
    @1
    @13
    cA
    cc
    wcel
    @14
    cA
    gzcn
    syl
    #
    abscld
    #
    recnd
    @2
    sqeq0
    syl
    @1
    @15
    cA
    cc0
    wceq
    #
    @8
    @1
    cA
    @16
    abs00ad
    @18
    @1
    @8
    cA
    cc0
    @0
    eleq1
    biimpcd
    sylbid
    sylbid
    syld
    mt3i
    nnge1d
    syl5eqbr
    @1
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    @3
    @6
    wb
    #
    @17
    @1
    cA
    @16
    absge0d
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @19
    @20
    wa
    @21
    1re
    0le1
    c1
    @2
    le2sq
    mpanl12
    syl2anc
    mpbird
end
