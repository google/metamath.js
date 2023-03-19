include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "ressxr.mm"
include "sstrd.mm"
include "adantr.mm"
include "supxrcld.mm"
include "syl5eqel.mm"
include "simpr.mm"
include "sseldd.mm"
include "mnfltd.mm"
include "sselda.mm"
include "cle.mm"
include "wbr.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "wceq.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "id.mm"
include "adantl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "xrleneltd.mm"
include "eliood.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem ressioosup
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let vx: setvar x
  assume ressioosup.a: |- ( ph -> A C_ RR )
  assume ressioosup.s: |- S = sup ( A , RR* , < )
  assume ressioosup.n: |- ( ph -> -. S e. A )
  assume ressioosup.i: |- I = ( -oo (,) S )


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
    cmnf
    cS
    cioo
    co
    cI
    @3
    cmnf
    cS
    @0
    cmnf
    cxr
    wcel
    @3
    mnfxr
    a1i
    @3
    cS
    cA
    cxr
    clt
    csup
    #
    cxr
    ressioosup.s
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
    ressioosup.a
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
    supxrcld
    syl5eqel
    #
    @3
    cA
    cr
    @0
    wph
    cA
    cr
    wss
    @2
    ressioosup.a
    adantr
    wph
    @2
    simpr
    #
    sseldd
    #
    @3
    @0
    @10
    mnfltd
    @3
    @0
    cS
    wph
    cA
    cxr
    @0
    @6
    sselda
    @8
    @3
    @0
    @4
    cS
    cle
    @3
    @5
    @2
    @0
    @4
    cle
    wbr
    @7
    @9
    cA
    @0
    supxrub
    syl2anc
    @3
    cS
    @4
    cS
    @4
    wceq
    @3
    ressioosup.s
    a1i
    eqcomd
    breqtrd
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
    ressioosup.n
    ad2antrr
    pm2.65da
    neqned
    xrleneltd
    eliood
    ressioosup.i
    syl6eleqr
    ralrimiva
    vx
    cA
    cI
    dfss3
    sylibr
end
