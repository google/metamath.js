include "ctau.mm"
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
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "df-tau.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "inss1.mm"
include "rpssre.mm"
include "sstri.mm"
include "taupilemrplb.mm"
include "cfv.mm"
include "wceq.mm"
include "2rp.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "mp2an.mm"
include "cos2pi.mm"
include "taupilem3.mm"
include "mpbir2an.mm"
include "infrelb.mm"
include "mp3an.mm"
include "eqbrtri.mm"

theorem taupilem2
  let vx: setvar x
  let vy: setvar y


  assert |- _tau <_ ( 2 x. _pi )

  proof
    ctau
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
    c2
    cpi
    cmul
    co
    #
    cle
    df-tau
    @1
    cr
    wss
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    @1
    wral
    vx
    cr
    wrex
    @3
    @1
    wcel
    #
    @2
    @3
    cle
    wbr
    @1
    crp
    cr
    crp
    @0
    inss1
    rpssre
    sstri
    vx
    vy
    @0
    taupilemrplb
    @4
    @3
    crp
    wcel
    #
    @3
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
    @5
    2rp
    pirp
    c2
    cpi
    rpmulcl
    mp2an
    cos2pi
    @3
    taupilem3
    mpbir2an
    vx
    vy
    @3
    @1
    infrelb
    mp3an
    eqbrtri
end
