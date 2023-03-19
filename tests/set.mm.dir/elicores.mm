include "cico.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "wrex.mm"
include "co.mm"
include "df-ico.mm"
include "reseq1i.mm"
include "wss.mm"
include "ressxr.mm"
include "resmpt2.mm"
include "mp2an.mm"
include "eqtri.mm"
include "rneqi.mm"
include "eleq2i.mm"
include "eqid.mm"
include "xrex.mm"
include "rabex.mm"
include "elrnmpt2.mm"
include "sseli.mm"
include "adantr.mm"
include "adantl.mm"
include "icoval.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "rexbiia.mm"
include "3bitri.mm"

theorem elicores
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A e. ran ( [,) |` ( RR X. RR ) ) <-> E. x e. RR E. y e. RR A = ( x [,) y ) )

  proof
    cA
    cico
    cr
    cr
    cxp
    #
    cres
    #
    crn
    #
    wcel
    cA
    vx
    vy
    cr
    cr
    vx
    cv
    #
    vz
    cv
    #
    cle
    wbr
    @4
    vy
    cv
    #
    clt
    wbr
    wa
    #
    vz
    cxr
    crab
    #
    cmpt2
    #
    crn
    #
    wcel
    cA
    @7
    wceq
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wrex
    cA
    @3
    @5
    cico
    co
    #
    wceq
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wrex
    @2
    @9
    cA
    @1
    @8
    @1
    vx
    vy
    cxr
    cxr
    @7
    cmpt2
    #
    @0
    cres
    #
    @8
    cico
    @15
    @0
    vx
    vy
    vz
    df-ico
    reseq1i
    cr
    cxr
    wss
    #
    @17
    @16
    @8
    wceq
    ressxr
    ressxr
    vx
    vy
    cxr
    cxr
    cr
    cr
    @7
    resmpt2
    mp2an
    eqtri
    rneqi
    eleq2i
    vx
    vy
    cr
    cr
    @7
    cA
    @8
    @8
    eqid
    @6
    vz
    cxr
    xrex
    rabex
    elrnmpt2
    @11
    @14
    vx
    cr
    @3
    cr
    wcel
    #
    @10
    @13
    vy
    cr
    @18
    @5
    cr
    wcel
    #
    wa
    #
    @7
    @12
    cA
    @20
    @12
    @7
    @20
    @3
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @12
    @7
    wceq
    @18
    @21
    @19
    cr
    cxr
    @3
    ressxr
    sseli
    adantr
    @19
    @22
    @18
    cr
    cxr
    @5
    ressxr
    sseli
    adantl
    vz
    @3
    @5
    icoval
    syl2anc
    eqcomd
    eqeq2d
    rexbidva
    rexbiia
    3bitri
end
