include "ctau.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "taupilem2.mm"
include "crp.mm"
include "ccos.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wcel.mm"
include "wb.mm"
include "inss1.mm"
include "rpssre.mm"
include "sstri.mm"
include "cfv.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "mp2an.mm"
include "cos2pi.mm"
include "taupilem3.mm"
include "mpbir2an.mm"
include "ne0ii.mm"
include "taupilemrplb.mm"
include "3pm3.2i.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "infregelb.mm"
include "wa.mm"
include "taupilem1.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "df-tau.mm"
include "breqtrri.mm"
include "infrecl.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "letri3i.mm"

theorem taupi
  let vx: setvar x
  let vy: setvar y


  assert |- _tau = ( 2 x. _pi )

  proof
    ctau
    c2
    cpi
    cmul
    co
    #
    wceq
    ctau
    @0
    cle
    wbr
    @0
    ctau
    cle
    wbr
    taupilem2
    @0
    crp
    ccos
    ccnv
    c1
    csn
    cima
    #
    cin
    #
    cr
    clt
    cinf
    #
    ctau
    cle
    @0
    @3
    cle
    wbr
    #
    @0
    vx
    cv
    #
    cle
    wbr
    #
    vx
    @2
    @2
    cr
    wss
    #
    @2
    c0
    wne
    #
    @5
    vy
    cv
    cle
    wbr
    vy
    @2
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    @0
    cr
    wcel
    @4
    @6
    vx
    @2
    wral
    wb
    @7
    @8
    @9
    @2
    crp
    cr
    crp
    @1
    inss1
    rpssre
    sstri
    @0
    @2
    @0
    @2
    wcel
    @0
    crp
    wcel
    #
    @0
    ccos
    cfv
    c1
    wceq
    c2
    crp
    wcel
    cpi
    crp
    wcel
    @11
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    cos2pi
    @0
    taupilem3
    mpbir2an
    ne0ii
    vx
    vy
    @1
    taupilemrplb
    3pm3.2i
    #
    c2
    cpi
    2re
    pire
    remulcli
    #
    vx
    vy
    vx
    @2
    @0
    infregelb
    mp2an
    @5
    @2
    wcel
    @5
    crp
    wcel
    @5
    ccos
    cfv
    c1
    wceq
    wa
    @6
    @5
    taupilem3
    @5
    taupilem1
    sylbi
    mprgbir
    df-tau
    breqtrri
    ctau
    @0
    ctau
    @3
    cr
    df-tau
    @10
    @3
    cr
    wcel
    @12
    vx
    vy
    @2
    infrecl
    ax-mp
    eqeltri
    @13
    letri3i
    mpbir2an
end
