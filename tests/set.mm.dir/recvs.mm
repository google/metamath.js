include "crefld.mm"
include "crglmod.mm"
include "cfv.mm"
include "cclm.mm"
include "clvec.mm"
include "cin.mm"
include "ccvs.mm"
include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "ccnfld.mm"
include "cr.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "crg.mm"
include "cfield.mm"
include "refld.mm"
include "cidom.mm"
include "fldidom.mm"
include "ccrg.mm"
include "cdomn.mm"
include "wa.mm"
include "isidom.mm"
include "crngring.mm"
include "adantr.mm"
include "sylbi.mm"
include "syl.mm"
include "ax-mp.mm"
include "rlmlmod.mm"
include "rlmsca.mm"
include "df-refld.mm"
include "eqtr3i.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "eqid.mm"
include "isclmi.mm"
include "mp3an.mm"
include "simpri.mm"
include "rlmlvec.mm"
include "elini.mm"
include "df-cvs.mm"
include "3eltr4i.mm"

theorem recvs
  let cR: class R
  assume recvs.r: |- R = ( ringLMod ` RRfld )


  assert |- R e. CVec

  proof
    crefld
    crglmod
    cfv
    #
    cclm
    clvec
    cin
    cR
    ccvs
    @0
    cclm
    clvec
    @0
    clmod
    wcel
    #
    @0
    csca
    cfv
    #
    ccnfld
    cr
    cress
    co
    #
    wceq
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @0
    cclm
    wcel
    crefld
    crg
    wcel
    #
    @1
    crefld
    cfield
    wcel
    #
    @5
    refld
    @6
    crefld
    cidom
    wcel
    #
    @5
    crefld
    fldidom
    @7
    crefld
    ccrg
    wcel
    #
    crefld
    cdomn
    wcel
    #
    wa
    @5
    crefld
    isidom
    @8
    @5
    @9
    crefld
    crngring
    adantr
    sylbi
    syl
    ax-mp
    crefld
    rlmlmod
    ax-mp
    crefld
    @2
    @3
    @6
    crefld
    @2
    wceq
    refld
    crefld
    cfield
    rlmsca
    ax-mp
    df-refld
    eqtr3i
    @4
    crefld
    cdr
    wcel
    #
    resubdrg
    simpli
    @2
    cr
    @0
    @2
    eqid
    isclmi
    mp3an
    @10
    @0
    clvec
    wcel
    @4
    @10
    resubdrg
    simpri
    crefld
    rlmlvec
    ax-mp
    elini
    recvs.r
    df-cvs
    3eltr4i
end
