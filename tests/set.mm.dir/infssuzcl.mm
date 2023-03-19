include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "sstr.mm"
include "mpan2.mm"
include "adantr.mm"
include "uzwo.mm"
include "lbinfcl.mm"
include "syl2anc.mm"

theorem infssuzcl
  let cS: class S
  let cM: class M
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( S C_ ( ZZ>= ` M ) /\ S =/= (/) ) -> inf ( S , RR , < ) e. S )

  proof
    cS
    cM
    cuz
    cfv
    #
    wss
    #
    cS
    c0
    wne
    #
    wa
    cS
    cr
    wss
    #
    vj
    cv
    vk
    cv
    cle
    wbr
    vk
    cS
    wral
    vj
    cS
    wrex
    cS
    cr
    clt
    cinf
    cS
    wcel
    @1
    @3
    @2
    @1
    @0
    cr
    wss
    @3
    @0
    cz
    cr
    cM
    uzssz
    zssre
    sstri
    cS
    @0
    cr
    sstr
    mpan2
    adantr
    cS
    vj
    vk
    cM
    uzwo
    vj
    vk
    cS
    lbinfcl
    syl2anc
end
