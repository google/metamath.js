include "lexicon.mm"

axiom ax-1
  let wph: wff ph
  let wps: wff ps
  assert |- ( ph -> ( ps -> ph ) )
end
