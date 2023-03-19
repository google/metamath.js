include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cr.mm"
include "ressxr.mm"
include "a1i.mm"
include "sstrd.mm"
include "adantr.mm"
include "infxrcld.mm"
include "syl5eqel.mm"
include "pnfxr.mm"
include "simpr.mm"
include "sseldd.mm"
include "sselda.mm"
include "cle.mm"
include "wbr.mm"
include "infxrlb.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"
include "wceq.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "necomd.mm"
include "xrleneltd.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem ressiooinf
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let vx: setvar x
  assume ressiooinf.a: |- ( ph -> A C_ RR )
  assume ressiooinf.s: |- S = inf ( A , RR* , < )
  assume ressiooinf.n: |- ( ph -> -. S e. A )
  assume ressiooinf.i: |- I = ( S (,) +oo )


  assert |- ( ph -> A C_ I )

  proof
    wph
    vx
    cv
    #
    cI
    wcel
    #
    vx
    cA
    wral
    cA
    cI
    wss
    wph
    @1
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @0
    cS
    cpnf
    cioo
    co
    cI
    @3
    cS
    cpnf
    @0
    @3
    cS
    cA
    cxr
    clt
    cinf
    #
    cxr
    ressiooinf.s
    @3
    cA
    wph
    cA
    cxr
    wss
    #
    @2
    wph
    cA
    cr
    cxr
    ressiooinf.a
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    #
    adantr
    #
    infxrcld
    syl5eqel
    #
    cpnf
    cxr
    wcel
    @3
    pnfxr
    a1i
    @3
    cA
    cr
    @0
    wph
    cA
    cr
    wss
    @2
    ressiooinf.a
    adantr
    wph
    @2
    simpr
    #
    sseldd
    #
    @3
    cS
    @0
    @8
    wph
    cA
    cxr
    @0
    @6
    sselda
    @3
    cS
    @4
    @0
    cle
    ressiooinf.s
    @3
    @5
    @2
    @4
    @0
    cle
    wbr
    @7
    @9
    cA
    @0
    infxrlb
    syl2anc
    syl5eqbr
    @3
    @0
    cS
    @3
    @0
    cS
    @3
    @0
    cS
    wceq
    #
    cS
    cA
    wcel
    #
    @2
    @11
    @12
    wph
    @2
    @11
    wa
    cS
    @0
    cA
    @11
    cS
    @0
    wceq
    @2
    @11
    @0
    cS
    @11
    id
    eqcomd
    adantl
    @2
    @11
    simpl
    eqeltrd
    adantll
    wph
    @12
    wn
    @2
    @11
    ressiooinf.n
    ad2antrr
    pm2.65da
    neqned
    necomd
    xrleneltd
    @3
    @0
    @10
    ltpnfd
    eliood
    ressiooinf.i
    syl6eleqr
    ralrimiva
    vx
    cA
    cI
    dfss3
    sylibr
end
