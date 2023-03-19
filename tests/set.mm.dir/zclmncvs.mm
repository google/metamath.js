include "cclm.mm"
include "wcel.mm"
include "ccvs.mm"
include "wnel.mm"
include "zring.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "csca.mm"
include "ccnfld.mm"
include "cz.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "crg.mm"
include "zringring.mm"
include "rlmlmod.mm"
include "ax-mp.mm"
include "rlmsca.mm"
include "df-zring.mm"
include "eqtr3i.mm"
include "zsubrg.mm"
include "eqid.mm"
include "isclmi.mm"
include "mp3an.mm"
include "eleq1i.mm"
include "mpbir.mm"
include "wn.mm"
include "clvec.mm"
include "wo.mm"
include "cdr.mm"
include "wa.mm"
include "zringndrg.mm"
include "neli.mm"
include "eqcomd.mm"
include "mtbir.mm"
include "intnan.mm"
include "islvec.mm"
include "olci.mm"
include "df-nel.mm"
include "cin.mm"
include "ianor.mm"
include "elin.mm"
include "xchnxbir.mm"
include "df-cvs.mm"
include "eleq12i.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem zclmncvs
  let cZ: class Z
  assume zclmncvs.z: |- Z = ( ringLMod ` ZZring )


  assert |- ( Z e. CMod /\ Z e/ CVec )

  proof
    cZ
    cclm
    wcel
    #
    cZ
    ccvs
    wnel
    #
    @0
    zring
    crglmod
    cfv
    #
    cclm
    wcel
    #
    @2
    clmod
    wcel
    #
    @2
    csca
    cfv
    #
    ccnfld
    cz
    cress
    co
    #
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @3
    zring
    crg
    wcel
    #
    @4
    zringring
    zring
    rlmlmod
    ax-mp
    zring
    @5
    @6
    @7
    zring
    @5
    wceq
    zringring
    zring
    crg
    rlmsca
    #
    ax-mp
    df-zring
    eqtr3i
    zsubrg
    @5
    cz
    @2
    @5
    eqid
    #
    isclmi
    mp3an
    cZ
    @2
    cclm
    zclmncvs.z
    eleq1i
    mpbir
    @1
    @3
    wn
    #
    @2
    clvec
    wcel
    #
    wn
    #
    wo
    #
    @12
    @10
    @11
    @4
    @5
    cdr
    wcel
    #
    wa
    @14
    @4
    @14
    zring
    cdr
    wcel
    zring
    cdr
    zringndrg
    neli
    @5
    zring
    cdr
    @7
    @5
    zring
    wceq
    zringring
    @7
    zring
    @5
    @8
    eqcomd
    ax-mp
    eleq1i
    mtbir
    intnan
    @5
    @2
    @9
    islvec
    mtbir
    olci
    @1
    cZ
    ccvs
    wcel
    #
    wn
    @13
    cZ
    ccvs
    df-nel
    @2
    cclm
    clvec
    cin
    #
    wcel
    #
    @13
    @15
    @3
    @11
    wa
    @13
    @17
    @3
    @11
    ianor
    @2
    cclm
    clvec
    elin
    xchnxbir
    cZ
    @2
    ccvs
    @16
    zclmncvs.z
    df-cvs
    eleq12i
    xchnxbir
    bitri
    mpbir
    pm3.2i
end
