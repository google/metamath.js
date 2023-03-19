include "cfn.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccusgr.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "cedg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resiexg.mm"
include "mp1i.mm"
include "sizusglecusglem1.mm"
include "f1eq1.mm"
include "spcegv.mm"
include "sylc.mm"
include "adantl.mm"
include "cdom.mm"
include "wb.mm"
include "hashdom.mm"
include "adantr.mm"
include "brdomg.mm"
include "bitrd.mm"
include "mpbird.mm"
include "exp31.mm"
include "wn.mm"
include "w3a.mm"
include "sizusglecusglem2.mm"
include "pm2.24d.mm"
include "3expia.mm"
include "com13.mm"
include "pm2.61i.mm"
include "nfile.mm"
include "mp3an12.mm"
include "a1d.mm"

theorem sizusglecusg
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  assume fusgrmaxsize.v: |- V = ( Vtx ` G )
  assume fusgrmaxsize.e: |- E = ( Edg ` G )
  assume usgrsscusgra.h: |- V = ( Vtx ` H )
  assume usgrsscusgra.f: |- F = ( Edg ` H )


  assert |- ( ( G e. USGraph /\ H e. ComplUSGraph ) -> ( # ` E ) <_ ( # ` F ) )

  proof
    cF
    cfn
    wcel
    #
    cG
    cusgr
    wcel
    #
    cH
    ccusgr
    wcel
    #
    wa
    #
    cE
    chash
    cfv
    cF
    chash
    cfv
    cle
    wbr
    #
    wi
    #
    cE
    cfn
    wcel
    #
    @0
    @5
    wi
    @6
    @0
    @3
    @4
    @6
    @0
    wa
    #
    @3
    wa
    #
    @4
    cE
    cF
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @3
    @11
    @7
    @3
    cid
    cE
    cres
    #
    cvv
    wcel
    #
    cE
    cF
    @12
    wf1
    #
    @11
    cE
    cvv
    wcel
    #
    @13
    @3
    cE
    cG
    cedg
    cfv
    cvv
    fusgrmaxsize.e
    cG
    cedg
    fvex
    eqeltri
    #
    cE
    cvv
    resiexg
    mp1i
    cE
    cF
    cG
    cH
    cV
    fusgrmaxsize.v
    fusgrmaxsize.e
    usgrsscusgra.h
    usgrsscusgra.f
    sizusglecusglem1
    @10
    @14
    vf
    @12
    cvv
    cE
    cF
    @9
    @12
    f1eq1
    spcegv
    sylc
    adantl
    @8
    @4
    cE
    cF
    cdom
    wbr
    #
    @11
    @7
    @4
    @17
    wb
    @3
    cE
    cF
    cfn
    hashdom
    adantr
    @7
    @17
    @11
    wb
    #
    @3
    @0
    @18
    @6
    cE
    cF
    cfn
    vf
    brdomg
    adantl
    adantr
    bitrd
    mpbird
    exp31
    @3
    @0
    @6
    wn
    #
    @4
    @1
    @2
    @0
    @19
    @4
    wi
    @1
    @2
    @0
    w3a
    @6
    @4
    cE
    cF
    cG
    cH
    cV
    fusgrmaxsize.v
    fusgrmaxsize.e
    usgrsscusgra.h
    usgrsscusgra.f
    sizusglecusglem2
    pm2.24d
    3expia
    com13
    pm2.61i
    @0
    wn
    #
    @4
    @3
    @15
    cF
    cvv
    wcel
    @20
    @4
    @16
    cF
    cH
    cedg
    cfv
    cvv
    usgrsscusgra.f
    cH
    cedg
    fvex
    eqeltri
    cE
    cF
    cvv
    cvv
    nfile
    mp3an12
    a1d
    pm2.61i
end
