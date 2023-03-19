include "cnx.mm"
include "cid.mm"
include "cn.mm"
include "cres.mm"
include "df-ndx.mm"
include "cc.mm"
include "wuncn.mm"
include "wss.mm"
include "nnsscn.mm"
include "a1i.mm"
include "wunss.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "wunf.mm"
include "syl5eqel.mm"

theorem wunndx
  let wph: wff ph
  let cU: class U
  assume wunndx.1: |- ( ph -> U e. WUni )
  assume wunndx.2: |- ( ph -> _om e. U )


  assert |- ( ph -> ndx e. U )

  proof
    wph
    cnx
    cid
    cn
    cres
    #
    cU
    df-ndx
    wph
    cn
    cn
    cU
    @0
    wunndx.1
    wph
    cc
    cn
    cU
    wunndx.1
    wph
    cU
    wunndx.1
    wunndx.2
    wuncn
    cn
    cc
    wss
    wph
    nnsscn
    a1i
    wunss
    #
    @1
    cn
    cn
    @0
    wf1o
    cn
    cn
    @0
    wf
    wph
    cn
    f1oi
    cn
    cn
    @0
    f1of
    mp1i
    wunf
    syl5eqel
end
