include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cmhm.mm"
include "ghmmhm.mm"
include "mhmco.mm"
include "syl2an.mm"
include "cgrp.mm"
include "wceq.mm"
include "ghmgrp1.mm"
include "ghmgrp2.mm"
include "ghmmhmb.mm"
include "syl2anr.mm"
include "eleqtrrd.mm"

theorem ghmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( T GrpHom U ) /\ G e. ( S GrpHom T ) ) -> ( F o. G ) e. ( S GrpHom U ) )

  proof
    cF
    cT
    cU
    cghm
    co
    wcel
    #
    cG
    cS
    cT
    cghm
    co
    wcel
    #
    wa
    cF
    cG
    ccom
    #
    cS
    cU
    cmhm
    co
    #
    cS
    cU
    cghm
    co
    #
    @0
    cF
    cT
    cU
    cmhm
    co
    wcel
    cG
    cS
    cT
    cmhm
    co
    wcel
    @2
    @3
    wcel
    @1
    cT
    cU
    cF
    ghmmhm
    cS
    cT
    cG
    ghmmhm
    cS
    cT
    cU
    cF
    cG
    mhmco
    syl2an
    @1
    cS
    cgrp
    wcel
    cU
    cgrp
    wcel
    @4
    @3
    wceq
    @0
    cS
    cT
    cG
    ghmgrp1
    cT
    cU
    cF
    ghmgrp2
    cS
    cU
    ghmmhmb
    syl2anr
    eleqtrrd
end
