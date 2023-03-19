include "c2.mm"
include "ceu.mm"
include "clt.mm"
include "wbr.mm"
include "c3.mm"
include "cle.mm"
include "wne.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "cn0.mm"
include "cfa.mm"
include "cfv.mm"
include "eqid.mm"
include "ege2le3.mm"
include "simpli.mm"
include "wcel.mm"
include "wn.mm"
include "cq.mm"
include "eirr.mm"
include "neli.mm"
include "nnq.mm"
include "mto.mm"
include "wceq.mm"
include "2nn.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "ax-mp.mm"
include "2re.mm"
include "ere.mm"
include "ltleni.mm"
include "mpbir2an.mm"
include "simpri.mm"
include "3nn.mm"
include "mpbii.mm"
include "3re.mm"
include "pm3.2i.mm"

theorem egt2lt3
  let vn: setvar n


  assert |- ( 2 < _e /\ _e < 3 )

  proof
    c2
    ceu
    clt
    wbr
    #
    ceu
    c3
    clt
    wbr
    #
    @0
    c2
    ceu
    cle
    wbr
    #
    ceu
    c2
    wne
    #
    @2
    ceu
    c3
    cle
    wbr
    #
    vn
    vn
    cn
    c2
    c1
    c2
    cdiv
    co
    vn
    cv
    #
    cexp
    co
    cmul
    co
    cmpt
    #
    vn
    cn0
    c1
    @5
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    @6
    eqid
    @7
    eqid
    ege2le3
    #
    simpli
    ceu
    cn
    wcel
    #
    wn
    #
    @3
    @9
    ceu
    cq
    wcel
    ceu
    cq
    eirr
    neli
    ceu
    nnq
    mto
    #
    @9
    ceu
    c2
    ceu
    c2
    wceq
    @9
    c2
    cn
    wcel
    2nn
    ceu
    c2
    cn
    eleq1
    mpbiri
    necon3bi
    ax-mp
    c2
    ceu
    2re
    ere
    ltleni
    mpbir2an
    @1
    @4
    c3
    ceu
    wne
    #
    @2
    @4
    @8
    simpri
    @10
    @12
    @11
    @9
    c3
    ceu
    c3
    ceu
    wceq
    c3
    cn
    wcel
    @9
    3nn
    c3
    ceu
    cn
    eleq1
    mpbii
    necon3bi
    ax-mp
    ceu
    c3
    ere
    3re
    ltleni
    mpbir2an
    pm3.2i
end
