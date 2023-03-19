include "ccnfld.mm"
include "cq.mm"
include "cress.mm"
include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cclm.mm"
include "clvec.mm"
include "cin.mm"
include "ccvs.mm"
include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "wceq.mm"
include "csubrg.mm"
include "crg.mm"
include "cdr.mm"
include "wa.mm"
include "qsubdrg.mm"
include "drngring.mm"
include "adantl.mm"
include "ax-mp.mm"
include "rlmlmod.mm"
include "simpri.mm"
include "rlmsca.mm"
include "eqcomd.mm"
include "simpli.mm"
include "eqid.mm"
include "isclmi.mm"
include "mp3an.mm"
include "rlmlvec.mm"
include "elini.mm"
include "df-cvs.mm"
include "3eltr4i.mm"

theorem qcvs
  let cQ: class Q
  assume qcvs.q: |- Q = ( ringLMod ` ( CCfld |`s QQ ) )


  assert |- Q e. CVec

  proof
    ccnfld
    cq
    cress
    co
    #
    crglmod
    cfv
    #
    cclm
    clvec
    cin
    cQ
    ccvs
    @1
    cclm
    clvec
    @1
    clmod
    wcel
    #
    @1
    csca
    cfv
    #
    @0
    wceq
    #
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    @1
    cclm
    wcel
    @0
    crg
    wcel
    #
    @2
    @5
    @0
    cdr
    wcel
    #
    wa
    @6
    qsubdrg
    @7
    @6
    @5
    @0
    drngring
    adantl
    ax-mp
    @0
    rlmlmod
    ax-mp
    @7
    @4
    @5
    @7
    qsubdrg
    simpri
    #
    @7
    @0
    @3
    @0
    cdr
    rlmsca
    eqcomd
    ax-mp
    @5
    @7
    qsubdrg
    simpli
    @3
    cq
    @1
    @3
    eqid
    isclmi
    mp3an
    @7
    @1
    clvec
    wcel
    @8
    @0
    rlmlvec
    ax-mp
    elini
    qcvs.q
    df-cvs
    3eltr4i
end
