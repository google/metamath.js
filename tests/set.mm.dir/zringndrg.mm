include "zring.mm"
include "cdr.mm"
include "wcel.mm"
include "c2.mm"
include "cui.mm"
include "cfv.mm"
include "cz.mm"
include "cabs.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "1ne2.mm"
include "nesymi.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "2re.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "eqeq1i.mm"
include "mtbir.mm"
include "intnan.mm"
include "zringunit.mm"
include "crg.mm"
include "csn.mm"
include "cdif.mm"
include "zringbas.mm"
include "eqid.mm"
include "zring0.mm"
include "isdrng.mm"
include "wne.mm"
include "2z.mm"
include "2ne0.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "id.mm"
include "syl5eleqr.mm"
include "simplbiim.mm"
include "mto.mm"
include "nelir.mm"

theorem zringndrg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ZZring e/ DivRing

  proof
    zring
    cdr
    zring
    cdr
    wcel
    #
    c2
    zring
    cui
    cfv
    #
    wcel
    #
    @2
    c2
    cz
    wcel
    #
    c2
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    @5
    @3
    @5
    c2
    c1
    wceq
    c1
    c2
    1ne2
    nesymi
    @4
    c2
    c1
    c2
    cr
    wcel
    cc0
    c2
    cle
    wbr
    @4
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    eqeq1i
    mtbir
    intnan
    c2
    zringunit
    mtbir
    @0
    zring
    crg
    wcel
    @1
    cz
    cc0
    csn
    cdif
    #
    wceq
    #
    @2
    cz
    zring
    @1
    cc0
    zringbas
    @1
    eqid
    zring0
    isdrng
    @7
    c2
    @6
    @1
    c2
    @6
    wcel
    @3
    c2
    cc0
    wne
    2z
    2ne0
    c2
    cz
    cc0
    eldifsn
    mpbir2an
    @7
    id
    syl5eleqr
    simplbiim
    mto
    nelir
end
