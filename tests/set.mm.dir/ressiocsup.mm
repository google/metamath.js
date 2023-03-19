include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cmnf.mm"
include "cioc.mm"
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
include "sselda.mm"
include "simpr.mm"
include "sseldd.mm"
include "mnfltd.mm"
include "cle.mm"
include "wbr.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "wceq.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "eliocd.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem ressiocsup
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let vx: setvar x
  assume ressiocsup.a: |- ( ph -> A C_ RR )
  assume ressiocsup.s: |- S = sup ( A , RR* , < )
  assume ressiocsup.e: |- ( ph -> S e. A )
  assume ressiocsup.5: |- I = ( -oo (,] S )


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
    cioc
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
    ressiocsup.s
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
    ressiocsup.a
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
    wph
    cA
    cxr
    @0
    @6
    sselda
    @3
    @0
    @3
    cA
    cr
    @0
    wph
    cA
    cr
    wss
    @2
    ressiocsup.a
    adantr
    wph
    @2
    simpr
    #
    sseldd
    mnfltd
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
    @8
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
    ressiocsup.s
    a1i
    eqcomd
    breqtrd
    eliocd
    ressiocsup.5
    syl6eleqr
    ralrimiva
    vx
    cA
    cI
    dfss3
    sylibr
end
