include "cdvds.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "clcm.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "cz.mm"
include "dvdszrcl.mm"
include "anim12i.mm"
include "anandir.mm"
include "sylibr.mm"
include "ancomd.mm"
include "wi.mm"
include "lcmdvds.mm"
include "3expb.mm"
include "mpcom.mm"
include "elin.mm"
include "wrel.mm"
include "wb.mm"
include "reldvds.mm"
include "elrelimasn.mm"
include "ax-mp.mm"
include "anbi12i.mm"
include "bitri.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "a1i.mm"
include "dvdslcm.mm"
include "syl2anc.mm"
include "simpld.mm"
include "cn0.mm"
include "lcmcl.mm"
include "nn0zd.mm"
include "nzss.mm"
include "mpbird.mm"
include "simprd.mm"
include "ssind.mm"
include "eqssd.mm"

theorem nzin
  let wph: wff ph
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume nzin.m: |- ( ph -> M e. ZZ )
  assume nzin.n: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( ( || " { M } ) i^i ( || " { N } ) ) = ( || " { ( M lcm N ) } ) )

  proof
    wph
    cdvds
    cM
    csn
    cima
    #
    cdvds
    cN
    csn
    cima
    #
    cin
    #
    cdvds
    cM
    cN
    clcm
    co
    #
    csn
    cima
    #
    @2
    @4
    wss
    wph
    vn
    @2
    @4
    cM
    vn
    cv
    #
    cdvds
    wbr
    #
    cN
    @5
    cdvds
    wbr
    #
    wa
    #
    @3
    @5
    cdvds
    wbr
    #
    @5
    @2
    wcel
    #
    @5
    @4
    wcel
    #
    @5
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    wa
    @8
    @9
    @8
    @15
    @12
    @8
    @13
    @12
    wa
    #
    @14
    @12
    wa
    #
    wa
    @15
    @12
    wa
    @6
    @16
    @7
    @17
    cM
    @5
    dvdszrcl
    cN
    @5
    dvdszrcl
    anim12i
    @13
    @14
    @12
    anandir
    sylibr
    ancomd
    @12
    @13
    @14
    @8
    @9
    wi
    @5
    cM
    cN
    lcmdvds
    3expb
    mpcom
    @10
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    @8
    @5
    @0
    @1
    elin
    @18
    @6
    @19
    @7
    cdvds
    wrel
    #
    @18
    @6
    wb
    reldvds
    cM
    @5
    cdvds
    elrelimasn
    ax-mp
    @20
    @19
    @7
    wb
    reldvds
    cN
    @5
    cdvds
    elrelimasn
    ax-mp
    anbi12i
    bitri
    @20
    @11
    @9
    wb
    reldvds
    @3
    @5
    cdvds
    elrelimasn
    ax-mp
    3imtr4i
    ssriv
    a1i
    wph
    @4
    @0
    @1
    wph
    @4
    @0
    wss
    cM
    @3
    cdvds
    wbr
    #
    wph
    @21
    cN
    @3
    cdvds
    wbr
    #
    wph
    @13
    @14
    @21
    @22
    wa
    nzin.m
    nzin.n
    cM
    cN
    dvdslcm
    syl2anc
    #
    simpld
    wph
    @3
    cM
    cz
    wph
    @3
    wph
    @13
    @14
    @3
    cn0
    wcel
    nzin.m
    nzin.n
    cM
    cN
    lcmcl
    syl2anc
    nn0zd
    #
    nzin.m
    nzss
    mpbird
    wph
    @4
    @1
    wss
    @22
    wph
    @21
    @22
    @23
    simprd
    wph
    @3
    cN
    cz
    @24
    nzin.n
    nzss
    mpbird
    ssind
    eqssd
end
