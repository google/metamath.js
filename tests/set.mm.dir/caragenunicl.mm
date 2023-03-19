include "c0.mm"
include "wceq.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "caragen0.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "cn.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "com.mm"
include "wrel.mm"
include "reldom.mm"
include "brrelex.mm"
include "mpan.mm"
include "syl.mm"
include "0sdomg.mm"
include "mpbird.mm"
include "cen.mm"
include "nnenom.mm"
include "ensymi.mm"
include "a1i.mm"
include "domentr.mm"
include "syl2anc.mm"
include "fodomr.mm"
include "wi.mm"
include "cfv.mm"
include "ciun.mm"
include "founiiun.mm"
include "c1.mm"
include "come.mm"
include "1zzd.mm"
include "nnuz.mm"
include "wf.mm"
include "fof.mm"
include "wss.mm"
include "fssd.mm"
include "carageniuncl.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "pm2.61dan.mm"

theorem caragenunicl
  let wph: wff ph
  let cS: class S
  let cO: class O
  let cX: class X
  let vn: setvar n
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  assume caragenunicl.o: |- ( ph -> O e. OutMeas )
  assume caragenunicl.s: |- S = ( CaraGen ` O )
  assume caragenunicl.y: |- ( ph -> X C_ S )
  assume caragenunicl.ctb: |- ( ph -> X ~<_ _om )


  assert |- ( ph -> U. X e. S )

  proof
    wph
    cX
    c0
    wceq
    #
    cX
    cuni
    #
    cS
    wcel
    #
    wph
    @0
    wa
    @1
    c0
    cS
    @0
    @1
    c0
    wceq
    wph
    @0
    @1
    c0
    cuni
    c0
    cX
    c0
    unieq
    uni0
    syl6eq
    adantl
    wph
    c0
    cS
    wcel
    @0
    wph
    cS
    cO
    caragenunicl.o
    caragenunicl.s
    caragen0
    adantr
    eqeltrd
    wph
    @0
    wn
    #
    wa
    wph
    cX
    c0
    wne
    #
    @2
    wph
    @3
    simpl
    @3
    @4
    wph
    cX
    c0
    neqne
    adantl
    wph
    @4
    wa
    #
    cn
    cX
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @2
    @5
    c0
    cX
    csdm
    wbr
    #
    cX
    cn
    cdom
    wbr
    #
    @8
    @5
    @9
    @4
    wph
    @4
    simpr
    @5
    cX
    cvv
    wcel
    #
    @9
    @4
    wb
    wph
    @11
    @4
    wph
    cX
    com
    cdom
    wbr
    #
    @11
    caragenunicl.ctb
    cdom
    wrel
    @12
    @11
    reldom
    cX
    com
    cdom
    brrelex
    mpan
    syl
    adantr
    cX
    cvv
    0sdomg
    syl
    mpbird
    wph
    @10
    @4
    wph
    @12
    com
    cn
    cen
    wbr
    #
    @10
    caragenunicl.ctb
    @13
    wph
    cn
    com
    nnenom
    ensymi
    a1i
    cX
    com
    cn
    domentr
    syl2anc
    adantr
    cn
    cX
    vf
    fodomr
    syl2anc
    @5
    @7
    @2
    vf
    wph
    @7
    @2
    wi
    @4
    wph
    @7
    @2
    wph
    @7
    wa
    #
    @1
    vn
    cn
    vn
    cv
    @6
    cfv
    ciun
    #
    cS
    @7
    @1
    @15
    wceq
    wph
    vn
    cn
    cX
    @6
    founiiun
    adantl
    @14
    cS
    vn
    @6
    c1
    cO
    cn
    wph
    cO
    come
    wcel
    @7
    caragenunicl.o
    adantr
    caragenunicl.s
    @14
    1zzd
    nnuz
    @14
    cn
    cX
    cS
    @6
    @7
    cn
    cX
    @6
    wf
    wph
    cn
    cX
    @6
    fof
    adantl
    wph
    cX
    cS
    wss
    @7
    caragenunicl.y
    adantr
    fssd
    carageniuncl
    eqeltrd
    ex
    adantr
    exlimdv
    mpd
    syl2anc
    pm2.61dan
end
