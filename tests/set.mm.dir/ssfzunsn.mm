include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "csn.mm"
include "cun.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "simp1.mm"
include "eluzel2.mm"
include "3ad2ant3.mm"
include "simp2.mm"
include "eluzelz.mm"
include "ssfzunsnext.mm"
include "syl13anc.mm"
include "wceq.mm"
include "eluz2.mm"
include "cxr.mm"
include "zre.mm"
include "rexrd.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "xrmineq.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "sylbi.mm"
include "oveq1d.mm"
include "sseqtr4d.mm"

theorem ssfzunsn
  let cS: class S
  let cI: class I
  let cM: class M
  let cN: class N


  assert |- ( ( S C_ ( M ... N ) /\ N e. ZZ /\ I e. ( ZZ>= ` M ) ) -> ( S u. { I } ) C_ ( M ... if ( I <_ N , N , I ) ) )

  proof
    cS
    cM
    cN
    cfz
    co
    wss
    #
    cN
    cz
    wcel
    #
    cI
    cM
    cuz
    cfv
    wcel
    #
    w3a
    #
    cS
    cI
    csn
    cun
    #
    cI
    cM
    cle
    wbr
    cI
    cM
    cif
    #
    cI
    cN
    cle
    wbr
    cN
    cI
    cif
    #
    cfz
    co
    #
    cM
    @6
    cfz
    co
    @3
    @0
    cM
    cz
    wcel
    #
    @1
    cI
    cz
    wcel
    #
    @4
    @7
    wss
    @0
    @1
    @2
    simp1
    @2
    @0
    @8
    @1
    cM
    cI
    eluzel2
    3ad2ant3
    @0
    @1
    @2
    simp2
    @2
    @0
    @9
    @1
    cM
    cI
    eluzelz
    3ad2ant3
    cS
    cI
    cM
    cN
    ssfzunsnext
    syl13anc
    @3
    cM
    @5
    @6
    cfz
    @2
    @0
    cM
    @5
    wceq
    #
    @1
    @2
    @8
    @9
    cM
    cI
    cle
    wbr
    #
    w3a
    #
    @10
    cM
    cI
    eluz2
    @12
    @5
    cM
    @12
    cI
    cxr
    wcel
    #
    cM
    cxr
    wcel
    #
    @11
    @5
    cM
    wceq
    @9
    @8
    @13
    @11
    @9
    cI
    cI
    zre
    rexrd
    3ad2ant2
    @8
    @9
    @14
    @11
    @8
    cM
    cM
    zre
    rexrd
    3ad2ant1
    @8
    @9
    @11
    simp3
    cI
    cM
    xrmineq
    syl3anc
    eqcomd
    sylbi
    3ad2ant3
    oveq1d
    sseqtr4d
end
